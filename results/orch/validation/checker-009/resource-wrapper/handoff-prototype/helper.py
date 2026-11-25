#!/usr/bin/env python3
"""Fork an environment-inheriting worker; control socket contains no environment data."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import signal
import socket
import sys
import threading

sys.dont_write_bytecode = True
SIGNALS = (signal.SIGINT, signal.SIGTERM, signal.SIGHUP, signal.SIGQUIT)


def load_worker(path):
    spec = importlib.util.spec_from_file_location("reviewed_resource_worker", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load reviewed resource worker")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def read_line(connection):
    data = bytearray()
    while len(data) <= 256:
        byte = connection.recv(1)
        if not byte:
            return None
        if byte == b"\n":
            return data.decode("ascii")
        data.extend(byte)
    raise RuntimeError("oversized control message")


def send_status(connection, status):
    connection.sendall(f"STATUS {status}\n".encode("ascii"))


def child(connection, config_path, argv):
    # Separate process group prevents a terminal/group signal from killing restoration.
    os.setsid()
    connection.sendall(f"READY {os.getpid()}\n".encode("ascii"))
    initial = read_line(connection)
    if initial is None:
        return 125
    if initial.startswith("SIGNAL "):
        number = int(initial.split()[1])
        if number not in SIGNALS:
            raise RuntimeError("unsupported control signal")
        send_status(connection, -number)
        return 128 + number
    if initial != "GO":
        raise RuntimeError("invalid readiness message")
    config = json.loads(Path(config_path).read_text())
    worker = load_worker(config["worker_module"])
    enter, restore = worker.load_config(config_path)
    runner = worker.Runner()
    finished = threading.Event()

    def watch_outer():
        try:
            while not finished.is_set():
                line = read_line(connection)
                if line is None:
                    if not finished.is_set():
                        os.kill(os.getpid(), signal.SIGTERM)
                    return
                if not line.startswith("SIGNAL "):
                    os.kill(os.getpid(), signal.SIGTERM)
                    return
                number = int(line.split()[1])
                if number not in SIGNALS:
                    os.kill(os.getpid(), signal.SIGTERM)
                    return
                os.kill(os.getpid(), number)
        except (OSError, ValueError, RuntimeError):
            if not finished.is_set():
                os.kill(os.getpid(), signal.SIGTERM)

    watcher = threading.Thread(target=watch_outer, daemon=True)
    watcher.start()
    try:
        status = runner.supervise(enter, argv, restore)
        finished.set()
        try:
            send_status(connection, status)
        except (BrokenPipeError, ConnectionResetError):
            pass
        return status if status >= 0 else 128 - status
    finally:
        finished.set()
        try:
            connection.shutdown(socket.SHUT_RDWR)
        except OSError:
            pass
        connection.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--socket", required=True)
    parser.add_argument("--config", required=True)
    parser.add_argument("verifier", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    argv = args.verifier
    if argv and argv[0] == "--":
        argv = argv[1:]
    if not argv:
        parser.error("verifier argv is required")
    connection = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    connection.connect(args.socket)
    pid = os.fork()
    if pid:
        # Do not wait for the worker: real Lake must be allowed to exit first.
        connection.close()
        os._exit(0)
    try:
        result = child(connection, args.config, argv)
    except BaseException as error:
        print(f"handoff-helper: worker fault: {type(error).__name__}: {error}", file=sys.stderr)
        try:
            send_status(connection, 125)
        except OSError:
            pass
        result = 125
    os._exit(result)


if __name__ == "__main__":
    main()
