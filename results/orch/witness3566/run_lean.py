#!/usr/bin/env python3
import argparse
import resource
import subprocess
import time
from pathlib import Path

p = argparse.ArgumentParser(description='Run Lean and preserve diagnostics and Linux resource usage.')
p.add_argument('lean_file', type=Path)
p.add_argument('log_file', type=Path)
args = p.parse_args()
lean_file = args.lean_file.resolve()
start = time.monotonic()
with args.log_file.open('w') as log:
    result = subprocess.run(
        ['lake', 'env', 'lean', '--profile', '-j', '1', '-M', '5800', '-R', str(lean_file.parent), str(lean_file),
         '-o', str(lean_file.with_suffix('.olean'))],
        cwd='/workspace/pequalnp-proofs/lean', stdout=log, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - start
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    log.write(f'\nRESULT exit={result.returncode} elapsed_seconds={elapsed:.3f} max_rss_kib={rss}\n')
print(f'exit={result.returncode} elapsed_seconds={elapsed:.3f} max_rss_kib={rss}')
raise SystemExit(result.returncode)
