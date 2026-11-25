import datetime
import hashlib
import json
import math
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

folder = Path(__file__).resolve().parent
root = folder.parent
previous = json.loads((root / 'budget-floor13-run-2056.json').read_text())
assert previous['status'].startswith('UNKNOWN') or previous['status'] == 'unsat'
assert not Path('/proc/41172').exists()
expected = {
    'exact66_69_local.cpp': '79f7abdd4d8171bc60e357f9176ebad697a19ff7493fa49ec075b4ea4b4c67a8',
    'exact66_69_seeds.hpp': '18b99fe7a0ad0026dfd4016f2903ea4932b488088e13c7ca7eba7795e49d8d8b',
    'exact66_69_local': '2cf1d2c49c4e2ebee1a889633ed3ed41459d71744247df278896a8ccda87431a',
    'rows.txt': '535859e22fe4f5f187c9655d3ba3ad15e4b6d967b51b4981eba9d56925f62f48',
}
for name, digest in expected.items():
    assert hashlib.sha256((folder / name).read_bytes()).hexdigest() == digest
deadline = datetime.datetime.fromisoformat('2026-11-25T19:55:00+00:00')
now = datetime.datetime.now(datetime.timezone.utc)
seconds = min(600, math.floor((deadline-now).total_seconds())-3)
assert seconds > 0
prefix = folder / 'final-local66-69-2056'
command = [str(folder / 'exact66_69_local'), str(folder / 'rows.txt'), str(seconds), '205666']
record = {'source_hashes': expected, 'command': command, 'seconds_requested': seconds,
          'absolute_stop_utc': deadline.isoformat(), 'root_renewal_utc': '2026-11-25T19:43:41+00:00',
          'root_lease_expiry_utc': '2026-11-25T20:03:40.804+00:00',
          'scope': 'Exact-function local search; no nonRead1 or shared-dirty retention constraint.',
          'starting_state': '66 gates with seven jointRead1 failures and one dirty AND; restart pool also includes audited69 and read1 startup65.'}
interrupted = False
timed_out = False
started = time.monotonic()
with open(str(prefix)+'.stdout', 'w') as stdout, open(str(prefix)+'.stderr', 'w') as stderr:
    proc = subprocess.Popen(command, stdout=stdout, stderr=stderr, cwd=folder, start_new_session=True)
    record.update({'native_pid': proc.pid, 'wrapper_pid': os.getpid(),
                   'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()})
    Path(str(prefix)+'.launch.json').write_text(json.dumps(record, indent=2)+'\n')
    def stop(signum, frame):
        global interrupted
        interrupted = True
        if proc.poll() is None:
            os.killpg(proc.pid, signal.SIGTERM)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    try:
        remaining = max(0.1, (deadline-datetime.datetime.now(datetime.timezone.utc)).total_seconds())
        result = proc.wait(timeout=remaining)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(proc.pid, signal.SIGTERM)
        result = proc.wait()
record.update({'ended_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'wall_seconds': time.monotonic()-started, 'returncode': result,
               'interrupted': interrupted, 'absolute_timeout': timed_out,
               'maximum_rss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss})
Path(str(prefix)+'.result.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps(record))
