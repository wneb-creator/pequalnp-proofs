#!/usr/bin/env python3
"""Run storage phases around an unmodified subprocess, restoring on failure."""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import sys

RESTORE_FAILED = 125
LAUNCH_FAILED = 127
FORWARDED_SIGNALS = (signal.SIGINT, signal.SIGTERM, signal.SIGHUP, signal.SIGQUIT)


def load_config(path):
    config = json.loads(Path(path).read_text())
    commands = []
    for field in ("phase_enter", "phase_restore"):
        command = config[field]
        if (not isinstance(command, list) or not command or
                not all(isinstance(arg, str) and "\0" not in arg for arg in command) or
                not os.path.isabs(command[0])):
            raise ValueError(f"{field} must be a nonempty argv with an absolute executable")
        commands.append(command)
    return commands


class Runner:
    def __init__(self):
        self.child = None
        self.restoring = False
        self.pending_signal = None

    def signal_received(self, number, frame):
        del frame
        if self.pending_signal is None:
            self.pending_signal = number
        if not self.restoring and self.child is not None:
            try:
                self.child.send_signal(number)
            except ProcessLookupError:
                pass

    def run(self, command):
        try:
            self.child = subprocess.Popen(command)
        except OSError as error:
            print(f"resource-worker: cannot start process: {error}", file=sys.stderr)
            return LAUNCH_FAILED
        try:
            if self.pending_signal is not None and not self.restoring:
                try:
                    self.child.send_signal(self.pending_signal)
                except ProcessLookupError:
                    pass
            return self.child.wait()
        finally:
            self.child = None

    def supervise(self, enter, verifier, restore):
        old_handlers = {s: signal.signal(s, self.signal_received) for s in FORWARDED_SIGNALS}
        result = LAUNCH_FAILED
        restore_result = RESTORE_FAILED
        try:
            # Restore even when enter fails: enter may have completed only partly.
            try:
                result = self.run(enter)
                if result == 0:
                    if self.pending_signal is None:
                        result = self.run(verifier)
                    else:
                        result = -self.pending_signal
            finally:
                # A cancellation must not interrupt restoring the toolchain.
                self.restoring = True
                restore_result = self.run(restore)
        finally:
            for number, handler in old_handlers.items():
                signal.signal(number, handler)
        if restore_result != 0:
            print(f"resource-worker: storage restoration failed with status {restore_result}",
                  file=sys.stderr)
            return RESTORE_FAILED
        return result


def finish(status):
    if status < 0:
        number = -status
        if number not in (signal.SIGKILL, signal.SIGSTOP):
            signal.signal(number, signal.SIG_DFL)
        os.kill(os.getpid(), number)
        return 128 + number
    return status


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True)
    parser.add_argument("verifier", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    verifier = args.verifier
    if verifier and verifier[0] == "--":
        verifier = verifier[1:]
    if not verifier:
        parser.error("an exact verifier argv is required after --")
    try:
        enter, restore = load_config(args.config)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"resource-worker: invalid configuration: {error}", file=sys.stderr)
        return RESTORE_FAILED
    return finish(Runner().supervise(enter, verifier, restore))


if __name__ == "__main__":
    sys.exit(main())
