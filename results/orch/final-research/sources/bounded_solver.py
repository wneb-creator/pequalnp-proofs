#!/usr/bin/env python3
"""Run one existing CaDiCaL instance with hard address-space/CPU caps."""
import argparse
import datetime
import hashlib
import json
import resource
import subprocess
import time
from pathlib import Path


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--solver", type=Path, required=True)
    p.add_argument("--cnf", type=Path, required=True)
    p.add_argument("--seconds", type=int, required=True)
    p.add_argument("--memory-mib", type=int, required=True)
    p.add_argument("--prefix", type=Path, required=True)
    p.add_argument("--plain", action="store_true")
    args = p.parse_args()
    cap = args.memory_mib * 1024 * 1024

    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
        resource.setrlimit(resource.RLIMIT_CPU, (args.seconds + 10, args.seconds + 10))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    started_utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
    started = time.monotonic()
    with args.prefix.with_suffix(".log").open("wb") as f:
        command = [str(args.solver)] + (["--plain"] if args.plain else [])
        command += ["-t", str(args.seconds), str(args.cnf)]
        run = subprocess.run(command,
                             preexec_fn=limits, stdout=f, stderr=subprocess.STDOUT)
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    metadata = {"started_utc": started_utc, "seconds_limit": args.seconds,
                "address_space_limit_mib": args.memory_mib, "plain": args.plain,
                "exit_code": run.returncode,
                "elapsed_seconds": time.monotonic() - started,
                "peak_child_rss_kib": usage.ru_maxrss,
                "cnf_path": str(args.cnf), "cnf_bytes": args.cnf.stat().st_size,
                "cnf_sha256": hashlib.sha256(args.cnf.read_bytes()).hexdigest(),
                "stdout_stderr_log": str(args.prefix.with_suffix(".log"))}
    args.prefix.with_suffix(".json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps(metadata))


if __name__ == "__main__":
    main()
