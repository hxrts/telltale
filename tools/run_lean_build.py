#!/usr/bin/env python3
"""Project adapter: retain its actual writer lease through the selected child."""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import sys
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
SUPPORTED_PROTOCOLS = {"1", "2"}
# Original admitted Wt1HhI profile: one worker7144 + original overhead1024.
# This is the complete v2 charge, not the ledger's v1 compatibility weight.
ORIGINAL_CHARGE_MIB = 8168


def executable(path: Path) -> bool:
    return path.is_file() and os.access(path, os.X_OK)


def selection() -> tuple[Path, str]:
    wrapper = Path(os.environ.get(
        "LEAN_BUILDER_BUILD_WRAPPER", ROOT.parent / "lean-builder/scripts/run-lean-build.py"
    ))
    binary = Path(os.environ.get(
        "LEAN_BUILDER_BIN", ROOT.parent / "lean-builder/target/release/lean-builder"
    ))
    protocol = os.environ.get("LEAN_BUILDER_BUILD_PROTOCOL_VERSION", "1")
    if protocol not in SUPPORTED_PROTOCOLS:
        raise ValueError(f"incompatible build-budget protocol {protocol}")
    if not executable(wrapper):
        return wrapper, f"shared wrapper unavailable at {wrapper}"
    if not executable(binary):
        return wrapper, f"coordinator binary unavailable at {binary}"
    return wrapper, ""



def scoped_id(path: Path) -> str:
    # Existing shared-resource namespace, identical to its canonical producer.
    # This identifies scheduling resources. Original FDs retain actual custody.
    return hashlib.sha256(str(path.resolve()).encode()).hexdigest()[:16]


def one_worker_profile() -> None:
    for name in ("LEAN_NUM_THREADS", "LEAN_BUILDER_BUILD_DESIRED_COUNT", "LEAN_BUILDER_BUILD_FLOOR"):
        if os.environ.get(name, "1") != "1":
            raise ValueError(f"original one-worker profile required: {name}")


def native_profile_fits() -> None:
    # A configuration is no machine grant. Refuse unknown/insufficient selected
    # capacity rather than silently running an unproved heavy degraded profile.
    try:
        capacity = int(os.environ["LEAN_BUILDER_BUILD_CAPACITY_MIB"])
        reserve = int(os.environ["LEAN_BUILDER_BUILD_RESERVE_MIB"])
    except (KeyError, ValueError) as error:
        raise ValueError("original degraded resource capacity is unknown") from error
    if capacity < ORIGINAL_CHARGE_MIB or reserve < 4096:
        raise ValueError("original degraded resource profile does not fit selected capacity/reserve")


def checked_request(label: str) -> dict[str, object]:
    common = subprocess.run(
        ["git", "-C", str(ROOT), "rev-parse", "--git-common-dir"],
        text=True, stdout=subprocess.PIPE, check=True,
    ).stdout.strip()
    if not common:
        raise ValueError("original repository resource identity is absent")
    repository = Path(common)
    if not repository.is_absolute():
        repository = ROOT / repository
    cache = Path(os.environ.get("LAKE_CACHE_DIR", ROOT.parent / "lean-builder/cache"))
    identity = os.environ.get("TELLTALE_LEAN_SOURCE_IDENTITY")
    if identity is not None and (len(identity) != 64 or any(c not in "0123456789abcdef" for c in identity)):
        raise ValueError("source identity must be the original admission fingerprint")
    worktree_id = scoped_id(ROOT)
    return {
        "schema": "lean-builder-resource-request-v2", "label": label,
        "owner": "telltale", "operation_class": "conservative-build",
        "worktree": str(ROOT.resolve()), "source_identity": identity,
        "reads": sorted([f"worktree:{worktree_id}:source", f"shared-cache:{scoped_id(cache)}:maintenance"]),
        "writes": sorted([f"worktree:{worktree_id}:lake-build", f"worktree:{worktree_id}:generated-metadata", f"worktree:{worktree_id}:audit-results",
                          f"repository:{scoped_id(repository)}:legacy-global-writer"]),
        "requested_mib": ORIGINAL_CHARGE_MIB, "hard_cap_mib": ORIGINAL_CHARGE_MIB,
        "backfill": "fifo",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--custody-mode", action="store_true")
    parser.add_argument("--label", required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a command is required after --")
    try:
        wrapper, reason = selection()
    except ValueError as error:
        print(str(error), file=sys.stderr)
        return 78
    mode = "native" if reason else "shared"
    # Pure configuration selection for the original Rust deadline owner. This
    # does not acquire a lease, execute Lean, or acknowledge physical cleanup.
    if args.custody_mode:
        print(mode, flush=True)
        return 0
    if os.environ.get("TELLTALE_LEAN_CUSTODY_MODE", mode) != mode:
        print("Lean cancellation configuration changed before original launch", file=sys.stderr)
        return 78
    protocol = os.environ.get("LEAN_BUILDER_BUILD_PROTOCOL_VERSION", "1")
    try:
        if protocol == "2":
            one_worker_profile()
        if protocol == "2" and reason:
            native_profile_fits()
        elif protocol == "2":
            if not Path("/dev/fd").is_dir():
                raise ValueError("original request descriptor transport unavailable")
            if not any((Path(part) / "ps").is_file() and os.access(Path(part) / "ps", os.X_OK)
                       for part in os.get_exec_path()):
                raise ValueError("original v2 process measurement provider ps unavailable")
            request_document = checked_request(args.label)
    except subprocess.CalledProcessError as error:
        print(str(error), file=sys.stderr)
        return error.returncode if error.returncode >= 0 else 128 - error.returncode
    except (ValueError, OSError) as error:
        print(str(error), file=sys.stderr)
        return 78
    count = os.environ.get("LEAN_NUM_THREADS", "1")
    if not count.isdecimal() or int(count) < 1:
        parser.error("LEAN_NUM_THREADS must be a positive integer")
    # Reuse the original degraded-writer lock for BOTH modes so a transition
    # between shared and degraded execution cannot overlap the old host child.
    lock_path = Path(os.environ.get(
        "TELLTALE_LOCAL_LAKE_LOCK", ROOT / "lean/.lake/build/telltale-build-launcher.lock"
    ))
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a+", encoding="utf-8") as lock:
        try:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            lock.seek(0)
            print(f"Telltale local Lake lock waiting: {lock.read().strip() or 'owner unknown'}",
                  file=sys.stderr, flush=True)
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        lock.seek(0)
        lock.truncate()
        lock.write(json.dumps({"pid": os.getpid(), "label": args.label}, sort_keys=True) + "\n")
        lock.flush()
        descriptor = lock.fileno()
        os.set_inheritable(descriptor, True)
        environment = os.environ.copy()
        if reason:
            print(f"Telltale build coordination degraded: {reason}; using local mutex with "
                  f"LEAN_NUM_THREADS={count}; machine-wide exclusion is unavailable",
                  file=sys.stderr, flush=True)
            environment["LEAN_NUM_THREADS"] = count
            invocation = command
        elif protocol == "1":
            # Preserve the original selected v1 contract and caller worker set.
            invocation = [str(wrapper), "--required-child-custody-version", "1",
                          "--pass-fd", str(descriptor), "--label", args.label,
                          "--desired-count", os.environ.get("LEAN_BUILDER_BUILD_DESIRED_COUNT", count),
                          "--floor", os.environ.get("LEAN_BUILDER_BUILD_FLOOR", "1"), "--", *command]
        else:
            # An unlinked owned descriptor prevents a mutable request pathname
            # from changing while queued. The existing chain retains BOTH FDs.
            with tempfile.TemporaryFile(mode="w+b") as request:
                request.write(json.dumps(request_document, sort_keys=True).encode())
                request.flush()
                request.seek(0)
                request_fd = request.fileno()
                os.set_inheritable(request_fd, True)
                invocation = [str(wrapper), "--required-child-custody-version", "1",
                              "--pass-fd", str(descriptor), "--pass-fd", str(request_fd),
                              "--protocol-version", "2", "--resource-request", f"/dev/fd/{request_fd}",
                              "--label", args.label, "--desired-count", "1", "--floor", "1", "--", *command]
                os.execvpe(invocation[0], invocation, environment)
        # Replace the unforwarded subprocess.run boundary. The original PID,
        # process group and actual lock FD continue into the selected owner.
        # Shared protocol v1 retains that FD through its lock/budget/timing chain.
        # It owns signal forwarding, escalation and physical child waits.
        os.execvpe(invocation[0], invocation, environment)
    raise AssertionError("exec returned without replacing the original host child")


if __name__ == "__main__":
    raise SystemExit(main())
