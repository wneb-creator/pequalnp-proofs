from datetime import datetime, timezone
from pathlib import Path
import fcntl
import hashlib
import json
import os
import resource
import signal
import subprocess
import sys
import time

root = Path('/tmp/oec/pequalnp-pilot-18')
here = root / 'orch/S03'
source = here / sys.argv[1]
label = sys.argv[2]
raw = source.read_bytes()
out = here / (label + '.stdout')
err = here / (label + '.stderr')
command = [str(root / 'lean-4.36.0-linux/bin/lake'), 'env', 'lean', '-M4000', '-j1', str(source)]
started = datetime.now(timezone.utc).isoformat()
waiting = time.monotonic()
with (root / 'orch-lean.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    acquired = time.monotonic()
    (here / (label + '.running.json')).write_text(json.dumps({'source': str(source), 'source_sha256': hashlib.sha256(raw).hexdigest(), 'started_utc': started, 'lock_acquired_utc': datetime.now(timezone.utc).isoformat(), 'command': command}, indent=2) + '\n')
    with out.open('wb') as stdout, err.open('wb') as stderr:
        process = subprocess.Popen(command, cwd='/workspace/pequalnp-proofs/lean', stdout=stdout, stderr=stderr, start_new_session=True)
        timeout = False
        try:
            code = process.wait(timeout=180)
        except subprocess.TimeoutExpired:
            timeout = True
            os.killpg(process.pid, signal.SIGTERM)
            try:
                code = process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                code = process.wait()
    elapsed = time.monotonic() - acquired
result = {'source': str(source), 'source_sha256': hashlib.sha256(raw).hexdigest(), 'source_unchanged': source.read_bytes() == raw,
          'command': command, 'workdir': '/workspace/pequalnp-proofs/lean', 'started_utc': started,
          'finished_utc': datetime.now(timezone.utc).isoformat(), 'lock_wait_seconds': acquired-waiting,
          'elapsed_seconds': elapsed, 'exit_code': code, 'timeout': timeout,
          'child_maxrss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
          'logs': {kind: {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'bytes': path.stat().st_size} for kind, path in [('stdout',out),('stderr',err)]}}
(here / (label + '.result.json')).write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
sys.exit(0 if code == 0 else 1)
