#!/usr/bin/env python3
"""Project adapter: retain its actual writer lease through the selected child."""
from __future__ import annotations

import argparse
import fcntl
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
SUPPORTED_PROTOCOL = "1"


def executable(path: Path) -> bool:
    return path.is_file() and os.access(path, os.X_OK)


def selection() -> tuple[Path, str]:
    wrapper = Path(os.environ.get(
        "LEAN_BUILDER_BUILD_WRAPPER", ROOT.parent / "lean-builder/scripts/run-lean-build.py"
    ))
    binary = Path(os.environ.get(
        "LEAN_BUILDER_BIN", ROOT.parent / "lean-builder/target/release/lean-builder"
    ))
    protocol = os.environ.get("LEAN_BUILDER_BUILD_PROTOCOL_VERSION", SUPPORTED_PROTOCOL)
    if protocol != SUPPORTED_PROTOCOL:
        return wrapper, f"incompatible build-budget protocol {protocol}"
    if not executable(wrapper):
        return wrapper, f"shared wrapper unavailable at {wrapper}"
    if not executable(binary):
        return wrapper, f"coordinator binary unavailable at {binary}"
    return wrapper, ""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--custody-mode", action="store_true")
    parser.add_argument("--label", required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a command is required after --")
    wrapper, reason = selection()
    mode = "native" if reason else "shared"
    # Pure configuration selection for the original Rust deadline owner. This
    # does not acquire a lease, execute Lean, or acknowledge physical cleanup.
    if args.custody_mode:
        print(mode, flush=True)
        return 0
    if os.environ.get("TELLTALE_LEAN_CUSTODY_MODE", mode) != mode:
        print("Lean cancellation configuration changed before original launch", file=sys.stderr)
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
        else:
            invocation = [str(wrapper), "--required-child-custody-version", "1",
                          "--pass-fd", str(descriptor), "--label", args.label,
                          "--desired-count", os.environ.get("LEAN_BUILDER_BUILD_DESIRED_COUNT", count),
                          "--floor", os.environ.get("LEAN_BUILDER_BUILD_FLOOR", "1"), "--", *command]
        # Replace the unforwarded subprocess.run boundary. The original PID,
        # process group and actual lock FD continue into the selected owner.
        # Shared protocol v1 retains that FD through its lock/budget/timing chain.
        # It owns signal forwarding, escalation and physical child waits.
        os.execvpe(invocation[0], invocation, environment)
    raise AssertionError("exec returned without replacing the original host child")


if __name__ == "__main__":
    raise SystemExit(main())
