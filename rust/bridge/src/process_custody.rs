//! Physical child settlement for the existing Lean bridge runner family.
use std::io::Write;
use std::io::{self, Read};
use std::process::{Child, Command, ExitStatus, Output};
use std::sync::mpsc::{self, Sender};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

#[derive(Debug, thiserror::Error)]
#[error("Lean child wait failed; timed_out={timed_out}; cleanup={cleanup:?}")]
pub(crate) struct Failure {
    pub(crate) timed_out: bool,
    #[source]
    pub(crate) primary: Option<io::Error>,
    pub(crate) cleanup: Vec<io::Error>,
    pub(crate) child_status: Option<ExitStatus>,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: Vec<u8>,
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::process::Stdio;

    #[test]
    fn exited_leader_remains_waitable_while_original_reader_is_gated() {
        struct GatedEof {
            stream: std::process::ChildStdout,
            reached: mpsc::Sender<()>,
            release: mpsc::Receiver<()>,
        }
        impl Read for GatedEof {
            fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
                let count = self.stream.read(bytes)?;
                if count == 0 {
                    self.reached.send(()).unwrap();
                    self.release.recv().unwrap();
                }
                Ok(count)
            }
        }
        let mut child = command("/bin/sh")
            .args(["-c", "printf retained; exit 41"])
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let (reached, observe) = mpsc::channel();
        let (release, gate) = mpsc::channel();
        let (errors, _) = mpsc::channel();
        let original_reader = reader(
            GatedEof {
                stream: child.stdout.take().unwrap(),
                reached,
                release: gate,
            },
            errors,
            &mut IoSpawner::default(),
        )
        .unwrap();
        observe.recv().unwrap();
        assert!(!original_reader.is_finished());
        // Actual kernel exit acknowledgment without returning the original PID.
        let pid = child.id() as libc::id_t;
        // Safety: C siginfo_t permits all-zero integer and pointer fields.
        let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
        assert_eq!(
            // Safety: info is writable; WNOWAIT observes the original child without reaping it.
            unsafe { libc::waitid(libc::P_PID, pid, &mut info, libc::WEXITED | libc::WNOWAIT) },
            0
        );
        let pending = poll_settled(&mut child, original_reader.is_finished());
        // Old eager try_wait reaps here: this second native waitid returns ECHILD.
        // Safety: info remains writable and WNOWAIT retains the original child PID.
        let still_owned =
            unsafe { libc::waitid(libc::P_PID, pid, &mut info, libc::WEXITED | libc::WNOWAIT) };
        let native_error = io::Error::last_os_error();
        release.send(()).unwrap();
        assert_eq!(original_reader.join().unwrap(), b"retained");
        assert!(pending.unwrap().is_none());
        assert_eq!(
            still_owned, 0,
            "original leader custody lost: {native_error}"
        );
        assert_eq!(
            poll_settled(&mut child, true).unwrap().unwrap().code(),
            Some(41)
        );
    }

    #[test]
    fn externally_reaped_original_has_no_false_cleanup_acknowledgment() {
        let mut child = command("/bin/sh").args(["-c", "exit 41"]).spawn().unwrap();
        let mut status = 0;
        assert_eq!(
            // Safety: status is writable; this test deliberately reaps its original OS child.
            unsafe { libc::waitpid(child.id() as libc::pid_t, &mut status, 0) },
            child.id() as libc::pid_t
        );
        let poll_error = poll_settled(&mut child, true).unwrap_err();
        assert_eq!(poll_error.raw_os_error(), Some(libc::ECHILD));
        let mut cleanup = Vec::new();
        assert!(wait_original(&mut child, &mut cleanup).is_none());
        assert_eq!(cleanup.len(), 1);
        assert_eq!(cleanup[0].raw_os_error(), Some(libc::ECHILD));
    }

    #[test]
    fn original_native_exit_and_separate_streams_survive() {
        let child = command("/bin/sh")
            .args(["-c", "printf stdout; printf stderr >&2; exit 41"])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let output = wait(child, Duration::from_secs(5)).unwrap();
        assert_eq!(output.status.code(), Some(41));
        assert_eq!(output.stdout, b"stdout");
        assert_eq!(output.stderr, b"stderr");
    }

    #[test]
    fn acknowledged_original_child_is_settled_before_timeout_returns() {
        let mut child = command("/bin/sh")
            .args(["-c", "printf R; exec /bin/sleep 30"])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let mut original_stdout = child.stdout.take().unwrap();
        let mut acknowledgment = [0];
        original_stdout.read_exact(&mut acknowledgment).unwrap();
        assert_eq!(acknowledgment, [b'R']);
        child.stdout = Some(original_stdout);
        let failure = wait(child, Duration::ZERO).unwrap_err();
        assert!(failure.timed_out);
        assert!(failure.primary.is_none());
        assert!(failure.cleanup.is_empty());
        assert!(failure.child_status.is_some());
    }

    #[test]
    fn native_ignored_term_is_escalated_and_partial_streams_survive() {
        use std::os::unix::process::ExitStatusExt;
        let mut child = command("/bin/sh")
            .args([
                "-c",
                "trap '' TERM; printf retained-stderr >&2; printf R; exec /bin/sleep 30",
            ])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let mut stream = child.stdout.take().unwrap();
        let mut ack = [0];
        stream.read_exact(&mut ack).unwrap();
        assert_eq!(ack, [b'R']);
        child.stdout = Some(stream);
        let failure = wait(child, Duration::ZERO).unwrap_err();
        assert!(failure.timed_out);
        assert!(failure.primary.is_none());
        assert!(failure.cleanup.is_empty());
        assert_eq!(failure.child_status.unwrap().signal(), Some(libc::SIGKILL));
        assert_eq!(failure.stderr, b"retained-stderr");
    }

    #[test]
    fn acknowledged_stdin_rejection_retains_original_io_source_and_settles() {
        let mut child = command("/bin/sh")
            .args(["-c", "exec 0<&-; printf R; exec /bin/sleep 30"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let mut stream = child.stdout.take().unwrap();
        let mut ack = [0];
        stream.read_exact(&mut ack).unwrap();
        assert_eq!(ack, [b'R']);
        child.stdout = Some(stream);
        let failure =
            wait_input(child, Duration::from_secs(5), false, vec![7; 1024 * 1024]).unwrap_err();
        assert!(!failure.timed_out);
        assert_eq!(
            failure.primary.as_ref().unwrap().raw_os_error(),
            Some(libc::EPIPE)
        );
        assert_eq!(
            std::error::Error::source(&failure)
                .unwrap()
                .downcast_ref::<io::Error>()
                .unwrap()
                .raw_os_error(),
            Some(libc::EPIPE)
        );
        assert!(failure.child_status.is_some());
    }

    fn selector_fixture(script: &str) -> (tempfile::TempDir, std::path::PathBuf) {
        use std::os::unix::fs::PermissionsExt;
        let directory = tempfile::tempdir().unwrap();
        std::fs::create_dir_all(directory.path().join("tools")).unwrap();
        std::fs::create_dir_all(directory.path().join("scripts/lean")).unwrap();
        let selector = directory.path().join("tools/run_lean_build.py");
        std::fs::write(&selector, script).unwrap();
        std::fs::set_permissions(&selector, std::fs::Permissions::from_mode(0o700)).unwrap();
        let launcher = directory
            .path()
            .join("scripts/lean/protocol-machine-runner.sh");
        (directory, launcher)
    }

    #[test]
    fn expired_custody_probe_is_not_spawned_after_positive_setup() {
        let (directory, launcher) =
            selector_fixture("#!/bin/sh\nprintf R > \"$0.executed\"; printf 'native\\n'\n");
        let marker = directory.path().join("tools/run_lean_build.py.executed");
        assert!(!select_custody(
            &mut command("true"),
            &launcher,
            true,
            Instant::now(),
            Duration::from_secs(5)
        )
        .unwrap());
        assert_eq!(std::fs::read(&marker).unwrap(), b"R");
        std::fs::remove_file(&marker).unwrap();
        let failure = select_custody(
            &mut command("true"),
            &launcher,
            true,
            Instant::now(),
            Duration::ZERO,
        )
        .unwrap_err();
        assert!(failure.timed_out);
        assert!(failure.primary.is_none());
        assert!(failure.cleanup.is_empty());
        assert!(failure.child_status.is_none());
        assert!(failure.stdout.is_empty());
        assert!(failure.stderr.is_empty());
        assert!(!marker.try_exists().unwrap());
    }

    #[test]
    fn custody_probe_retains_native_rejection_and_diagnostics() {
        let (_directory, launcher) = selector_fixture(
            "#!/bin/sh\nprintf original-out; printf original-error >&2; exit 41\n",
        );
        let failure = select_custody(
            &mut command("true"),
            &launcher,
            true,
            Instant::now(),
            Duration::from_secs(5),
        )
        .unwrap_err();
        assert!(!failure.timed_out);
        let source = failure.primary.unwrap();
        let native = source
            .get_ref()
            .unwrap()
            .downcast_ref::<SelectionFailure>()
            .unwrap();
        assert_eq!(native.status.code(), Some(41));
        assert_eq!(native.stdout, b"original-out");
        assert_eq!(native.stderr, b"original-error");
    }

    #[test]
    fn acknowledged_probe_uses_original_horizon_and_settles() {
        let (directory, launcher) =
            selector_fixture("#!/bin/sh\nprintf R > \"$0.ack\"; exec /bin/sleep 30\n");
        let fifo = directory.path().join("tools/run_lean_build.py.ack");
        let path = std::ffi::CString::new(fifo.as_os_str().as_encoded_bytes()).unwrap();
        // Safety: path is a valid NUL-terminated path; this creates the test FIFO.
        assert_eq!(unsafe { libc::mkfifo(path.as_ptr(), 0o600) }, 0);
        let started = Instant::now();
        let worker = std::thread::spawn(move || {
            select_custody(
                &mut command("true"),
                &launcher,
                true,
                started,
                Duration::from_secs(2),
            )
        });
        let mut ack = [0];
        std::fs::File::open(&fifo)
            .unwrap()
            .read_exact(&mut ack)
            .unwrap();
        assert_eq!(ack, [b'R']);
        let failure = worker.join().unwrap().unwrap_err();
        assert!(failure.timed_out);
        assert!(failure.child_status.is_some());
        assert!(failure.cleanup.is_empty());
        assert!(failure.primary.is_none());
    }

    fn startup_refusal_case(refusals: Vec<(usize, i32)>, expected: &[i32]) {
        use std::io::BufRead;
        let mut child = command("/bin/sh")
            .args([
                "-c",
                "trap 'exit 41' TERM; printf 'ready\\n'; read original; exit 41",
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let original = child.id();
        let mut ready = String::new();
        // Consume only the explicit setup acknowledgment on this original pipe.
        std::io::BufReader::new(child.stdout.as_mut().unwrap())
            .read_line(&mut ready)
            .unwrap();
        assert_eq!(ready, "ready\n");
        let failure = wait_owned_with_spawner(
            child,
            Duration::from_secs(5),
            false,
            Some(b"input\n".to_vec()),
            Instant::now(),
            IoSpawner {
                ordinal: 0,
                refusals,
            },
        )
        .unwrap_err();
        assert!(!failure.timed_out);
        assert_eq!(
            failure.primary.as_ref().unwrap().raw_os_error(),
            Some(expected[0])
        );
        let reported = failure
            .cleanup
            .iter()
            .filter_map(io::Error::raw_os_error)
            .collect::<Vec<_>>();
        assert!(reported.starts_with(&expected[1..]), "{reported:?}");
        assert_eq!(failure.child_status.unwrap().code(), Some(41));
        let mut native_status = 0;
        // Safety: waitpid observes only this fixture's actual original child id.
        assert_eq!(
            unsafe { libc::waitpid(original as libc::pid_t, &mut native_status, libc::WNOHANG) },
            -1
        );
        assert_eq!(
            io::Error::last_os_error().raw_os_error(),
            Some(libc::ECHILD)
        );
    }

    #[test]
    fn stdout_reader_start_refusal_settles_original_child() {
        startup_refusal_case(vec![(0, libc::EAGAIN)], &[libc::EAGAIN]);
    }

    #[test]
    fn stderr_reader_start_refusal_settles_original_child() {
        startup_refusal_case(vec![(1, libc::EAGAIN)], &[libc::EAGAIN]);
    }

    #[test]
    fn stdin_writer_start_refusal_settles_original_child() {
        startup_refusal_case(vec![(2, libc::EAGAIN)], &[libc::EAGAIN]);
    }

    #[test]
    fn partial_start_retains_original_and_independent_native_causes() {
        startup_refusal_case(
            vec![(0, libc::EAGAIN), (1, libc::ENOMEM), (2, libc::EPIPE)],
            &[libc::EAGAIN, libc::ENOMEM, libc::EPIPE],
        );
    }
}

// One per original physical wait owner; test faults are invocation-local and
// cannot affect parallel callers or production feature selection.
#[derive(Default)]
struct IoSpawner {
    #[cfg(test)]
    ordinal: usize,
    #[cfg(test)]
    refusals: Vec<(usize, i32)>,
}

impl IoSpawner {
    fn spawn<T: Send + 'static>(
        &mut self,
        name: &'static str,
        work: impl FnOnce() -> T + Send + 'static,
    ) -> io::Result<JoinHandle<T>> {
        #[cfg(test)]
        {
            let ordinal = self.ordinal;
            self.ordinal += 1;
            if let Some((_, native)) = self
                .refusals
                .iter()
                .find(|(selected, _)| *selected == ordinal)
            {
                return Err(io::Error::from_raw_os_error(*native));
            }
        }
        thread::Builder::new().name(name.to_string()).spawn(work)
    }
}

type Reader = JoinHandle<Vec<u8>>;

fn reader(
    stream: impl Read + Send + 'static,
    errors: Sender<io::Error>,
    spawner: &mut IoSpawner,
) -> io::Result<Reader> {
    spawner.spawn("lean-pipe-reader", move || {
        let mut stream = stream;
        let mut bytes = Vec::new();
        if let Err(error) = stream.read_to_end(&mut bytes) {
            // Receiver remains held until every original pipe owner is joined.
            let _ = errors.send(error);
        }
        bytes
    })
}

fn finish(handle: Option<Reader>, cleanup: &mut Vec<io::Error>) -> Vec<u8> {
    match handle.map(JoinHandle::join) {
        None => Vec::new(),
        Some(Ok(bytes)) => bytes,
        Some(Err(_)) => {
            cleanup.push(io::Error::other("original Lean pipe reader panicked"));
            Vec::new()
        }
    }
}

#[derive(Debug, thiserror::Error)]
#[error("original Lean custody selector failed {status}; stdout={stdout:?}; stderr={stderr:?}")]
struct SelectionFailure {
    status: ExitStatus,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

fn native_failure(error: io::Error) -> Failure {
    Failure {
        timed_out: false,
        primary: Some(error),
        cleanup: Vec::new(),
        child_status: None,
        stdout: Vec::new(),
        stderr: Vec::new(),
    }
}

pub(crate) fn begin_physical_horizon() -> Instant {
    Instant::now()
}

// This is admission to the original physical horizon, not a cleanup acknowledgment.
pub(crate) fn ensure_admission(started: Instant, timeout: Duration) -> Result<(), Failure> {
    if started.elapsed() >= timeout {
        return Err(Failure {
            timed_out: true,
            primary: None,
            cleanup: Vec::new(),
            child_status: None,
            stdout: Vec::new(),
            stderr: Vec::new(),
        });
    }
    Ok(())
}

pub(crate) fn select_custody(
    command: &mut Command,
    launcher: &std::path::Path,
    fallback: bool,
    started: Instant,
    timeout: Duration,
) -> Result<bool, Failure> {
    if !fallback {
        return Ok(false);
    }
    let selector = launcher
        .parent()
        .and_then(std::path::Path::parent)
        .and_then(std::path::Path::parent)
        .ok_or_else(|| native_failure(io::Error::other("canonical launcher has no project root")))?
        .join("tools/run_lean_build.py");
    let mut selector_command = self::command(selector);
    selector_command
        .args(["--custody-mode", "--label", "bridge-custody", "--", "true"])
        .env_remove("TELLTALE_LEAN_CUSTODY_MODE")
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    ensure_admission(started, timeout)?;
    let child = selector_command.spawn().map_err(native_failure)?;
    let result = wait_owned(child, timeout, false, None, started)?;
    if !result.status.success() {
        return Err(native_failure(io::Error::other(SelectionFailure {
            status: result.status,
            stdout: result.stdout,
            stderr: result.stderr,
        })));
    }
    let mode = match result.stdout.as_slice() {
        b"shared\n" => "shared",
        b"native\n" => "native",
        _ => {
            return Err(native_failure(io::Error::other(
                "invalid original custody configuration selection",
            )))
        }
    };
    command.env("TELLTALE_LEAN_CUSTODY_MODE", mode);
    Ok(mode == "shared")
}

pub(crate) fn command(program: impl AsRef<std::ffi::OsStr>) -> Command {
    let command = Command::new(program);
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        let mut command = command;
        command.process_group(0);
        command
    }
    #[cfg(not(unix))]
    command
}

// An unfinished pipe owner can outlive the entire original process group.
// Keep the original leader unreaped until no later group signal is possible.
// Callers must leave their signal loop immediately on Some or Err.
fn poll_settled(child: &mut Child, pipes_settled: bool) -> io::Result<Option<ExitStatus>> {
    if pipes_settled {
        child.try_wait()
    } else {
        Ok(None)
    }
}

// std Child::wait retries EINTR on Unix and retains its original native result.
// None is explicitly absent settlement evidence, including an externally reaped
// child (ECHILD); it must not be used to authorize a numeric group signal.
fn wait_original(child: &mut Child, cleanup: &mut Vec<io::Error>) -> Option<ExitStatus> {
    match child.wait() {
        Ok(status) => Some(status),
        Err(error) => {
            cleanup.push(error);
            None
        }
    }
}

fn cancel(child: &mut Child) -> io::Result<()> {
    #[cfg(unix)]
    {
        let pid = libc::pid_t::try_from(child.id())
            .map_err(|_| io::Error::other("original child pid is not representable"))?;
        // Request cancellation from the original wrapper; killing that sole
        // owner first would strand its project/lease and pipe-holding children.
        // Safety: kill takes scalar arguments; pid is this owned child's pid.
        if unsafe { libc::kill(-pid, libc::SIGTERM) } == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }
    #[cfg(not(unix))]
    {
        // Shared POSIX wrappers are unsupported here; retain existing native
        // direct-child behavior without claiming POSIX tree settlement.
        child.kill()
    }
}

pub(crate) fn wait(child: Child, timeout: Duration) -> Result<Output, Failure> {
    wait_owned(child, timeout, false, None, Instant::now())
}

#[cfg(test)]
pub(crate) fn wait_input(
    child: Child,
    timeout: Duration,
    shared: bool,
    input: Vec<u8>,
) -> Result<Output, Failure> {
    wait_owned(child, timeout, shared, Some(input), Instant::now())
}

pub(crate) fn wait_input_since(
    child: Child,
    timeout: Duration,
    shared: bool,
    input: Vec<u8>,
    started: Instant,
) -> Result<Output, Failure> {
    wait_owned(child, timeout, shared, Some(input), started)
}

fn wait_owned(
    child: Child,
    timeout: Duration,
    shared: bool,
    input: Option<Vec<u8>>,
    start: Instant,
) -> Result<Output, Failure> {
    wait_owned_with_spawner(child, timeout, shared, input, start, IoSpawner::default())
}

fn wait_owned_with_spawner(
    mut child: Child,
    timeout: Duration,
    shared: bool,
    input: Option<Vec<u8>>,
    start: Instant,
    mut spawner: IoSpawner,
) -> Result<Output, Failure> {
    let (errors, observed_errors) = mpsc::channel();
    let stdout =
        child.stdout.take().and_then(
            |stream| match reader(stream, errors.clone(), &mut spawner) {
                Ok(owner) => Some(owner),
                Err(error) => {
                    let _ = errors.send(error);
                    None
                }
            },
        );
    let stderr =
        child.stderr.take().and_then(
            |stream| match reader(stream, errors.clone(), &mut spawner) {
                Ok(owner) => Some(owner),
                Err(error) => {
                    let _ = errors.send(error);
                    None
                }
            },
        );
    let writer = input.and_then(|bytes| {
        child.stdin.take().and_then(|mut stream| {
            let producer = errors.clone();
            match spawner.spawn("lean-input-writer", move || {
                if let Err(error) = stream.write_all(&bytes) {
                    let _ = producer.send(error);
                }
            }) {
                Ok(owner) => Some(owner),
                Err(error) => {
                    let _ = errors.send(error);
                    None
                }
            }
        })
    });
    let mut failure = Failure {
        timed_out: false,
        primary: None,
        cleanup: Vec::new(),
        child_status: None,
        stdout: Vec::new(),
        stderr: Vec::new(),
    };
    let pipes_settled = || {
        stdout.as_ref().is_none_or(JoinHandle::is_finished)
            && stderr.as_ref().is_none_or(JoinHandle::is_finished)
            && writer.as_ref().is_none_or(JoinHandle::is_finished)
    };
    let status = loop {
        for error in observed_errors.try_iter() {
            if failure.primary.is_none() {
                failure.primary = Some(error);
            } else {
                failure.cleanup.push(error);
            }
        }
        match poll_settled(&mut child, pipes_settled()) {
            Ok(Some(status)) => break Some(status),
            Ok(_) if failure.primary.is_none() && start.elapsed() < timeout => {
                thread::sleep(Duration::from_millis(10));
                continue;
            }
            Err(error) => {
                let interrupted = error.kind() == io::ErrorKind::Interrupted;
                if failure.primary.is_none() {
                    failure.primary = Some(error);
                } else {
                    failure.cleanup.push(error);
                }
                if interrupted {
                    // No status was consumed. Retry the original observation;
                    // do not signal based on the failed poll.
                    continue;
                }
                // A failed poll cannot authorize numeric signaling. Retain the
                // original child through its actual wait, including ECHILD as
                // an independent loss-of-custody error, never an acknowledgment.
                break wait_original(&mut child, &mut failure.cleanup);
            }
            _ if failure.primary.is_none() => failure.timed_out = true,
            _ => {}
        }
        if let Err(error) = cancel(&mut child) {
            failure.cleanup.push(error);
        }
        if !shared {
            // Native/custom commands have no inner wrapper to escalate. Keep
            // the selected operation horizon fixed; this is physical cleanup
            // using the existing owner's two-second TERM grace.
            let cleanup_start = Instant::now();
            let settled = loop {
                match poll_settled(&mut child, pipes_settled()) {
                    Ok(Some(status)) => break Some(status),
                    Ok(_) if cleanup_start.elapsed() < Duration::from_secs(2) => {
                        thread::sleep(Duration::from_millis(10))
                    }
                    outcome => {
                        if let Err(error) = outcome {
                            let interrupted = error.kind() == io::ErrorKind::Interrupted;
                            failure.cleanup.push(error);
                            if interrupted {
                                continue;
                            }
                            break wait_original(&mut child, &mut failure.cleanup);
                        }
                        #[cfg(unix)]
                        {
                            if let Ok(pid) = libc::pid_t::try_from(child.id()) {
                                // Safety: this is the original group created by command().
                                if unsafe { libc::kill(-pid, libc::SIGKILL) } != 0 {
                                    failure.cleanup.push(io::Error::last_os_error());
                                }
                            }
                        }
                        #[cfg(not(unix))]
                        if let Err(error) = child.kill() {
                            failure.cleanup.push(error);
                        }
                        break match child.wait() {
                            Ok(status) => Some(status),
                            Err(error) => {
                                failure.cleanup.push(error);
                                None
                            }
                        };
                    }
                }
            };
            break settled;
        } else {
            // The canonical wrapper owns inner bounded group escalation. Never
            // hardkill its sole cleanup owner before its actual wait returns.
            match child.wait() {
                Ok(status) => break Some(status),
                Err(error) => {
                    failure.cleanup.push(error);
                    break None;
                }
            }
        }
    };
    failure.child_status = status;
    if let Some(writer) = writer {
        if writer.join().is_err() {
            failure
                .cleanup
                .push(io::Error::other("original Lean stdin writer panicked"));
        }
    }
    failure.stdout = finish(stdout, &mut failure.cleanup);
    failure.stderr = finish(stderr, &mut failure.cleanup);
    for error in observed_errors.try_iter() {
        if !failure.timed_out && failure.primary.is_none() {
            failure.primary = Some(error);
        } else {
            failure.cleanup.push(error);
        }
    }
    if !failure.timed_out && failure.primary.is_none() && !failure.cleanup.is_empty() {
        failure.primary = Some(failure.cleanup.remove(0));
    }
    if failure.timed_out || failure.primary.is_some() || !failure.cleanup.is_empty() {
        return Err(failure);
    }
    match status {
        Some(status) => Ok(Output {
            status,
            stdout: failure.stdout,
            stderr: failure.stderr,
        }),
        None => Err(failure),
    }
}
