#!/usr/bin/env python3
"""Telltale build launcher: shared lean-builder coordination or announced local fallback."""

from __future__ import annotations

import argparse
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
SUPPORTED_PROTOCOL = "1"


def executable(path: Path) -> bool:
    return path.is_file() and os.access(path, os.X_OK)


def degraded(label: str, command: list[str], reason: str) -> int:
    count = os.environ.get("LEAN_NUM_THREADS", "1")
    print(
        f"Telltale build coordination degraded: {reason}; "
        f"using local mutex with LEAN_NUM_THREADS={count}; "
        "machine-wide exclusion is unavailable",
        file=sys.stderr,
        flush=True,
    )
    lock_path = Path(os.environ.get(
        "TELLTALE_LOCAL_LAKE_LOCK", ROOT / "lean/.lake/build/telltale-build-launcher.lock"
    ))
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a+", encoding="utf-8") as lock:
        try:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            lock.seek(0)
            owner = lock.read().strip() or "owner unknown"
            print(f"Telltale local Lake lock waiting: {owner}", file=sys.stderr, flush=True)
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        lock.seek(0)
        lock.truncate()
        lock.write(json.dumps({"pid": os.getpid(), "label": label}, sort_keys=True) + "\n")
        lock.flush()
        environment = os.environ.copy()
        environment["LEAN_NUM_THREADS"] = count
        return subprocess.run(command, env=environment, check=False).returncode


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--label", required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a command is required after --")
    wrapper = Path(os.environ.get(
        "LEAN_BUILDER_BUILD_WRAPPER", ROOT.parent / "lean-builder/scripts/run-lean-build.py"
    ))
    binary = Path(os.environ.get(
        "LEAN_BUILDER_BIN", ROOT.parent / "lean-builder/target/release/lean-builder"
    ))
    protocol = os.environ.get("LEAN_BUILDER_BUILD_PROTOCOL_VERSION", SUPPORTED_PROTOCOL)
    if protocol != SUPPORTED_PROTOCOL:
        return degraded(args.label, command, f"incompatible build-budget protocol {protocol}")
    if not executable(wrapper):
        return degraded(args.label, command, f"shared wrapper unavailable at {wrapper}")
    if not executable(binary):
        return degraded(args.label, command, f"coordinator binary unavailable at {binary}")
    invocation = [str(wrapper), "--label", args.label,
                  "--desired-count", os.environ.get(
                      "LEAN_BUILDER_BUILD_DESIRED_COUNT", os.environ.get("LEAN_NUM_THREADS", "1")),
                  "--floor", os.environ.get("LEAN_BUILDER_BUILD_FLOOR", "1"),
                  "--", *command]
    return subprocess.run(invocation, check=False).returncode


if __name__ == "__main__":
    raise SystemExit(main())
