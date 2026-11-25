import json
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
import enc2_base
import validate

P = Path(__file__).resolve().parent
stop = P.parent / 'STOP'
assert not stop.exists() and not (P / 'STOP').exists()
assert json.loads((P / 'run1-record.json').read_text()).get('exit_code') == 0, 'Heuristic lane still active or cancelled'
seconds = int(sys.argv[1]) if len(sys.argv) > 1 else 900
assert seconds > 0
prefix = P / 'mono18-solve1'
assert not prefix.with_suffix('.stdout').exists() and not prefix.with_suffix('.lrat').exists()
assert shutil.disk_usage(P).free >= 6 * 1024**3, 'Insufficient initial disk reserve'
command = ['/tmp/oec/pequalnp-pilot-99/lean-4.36.0-linux/bin/cadical', '--lrat', '--binary', '-t', str(seconds),
           str(P / 'mono18-enc2.cnf'), str(prefix.with_suffix('.lrat'))]
record = {'started_utc': datetime.now(timezone.utc).isoformat(), 'command': command, 'seconds': seconds,
          'status_note': 'Solver exit10 means SAT;20 means UNSAT;0 means unresolved. Cancellation is recorded separately.'}
with prefix.with_suffix('.stdout').open('w') as out, prefix.with_suffix('.stderr').open('w') as err:
    child = subprocess.Popen(command, stdout=out, stderr=err)
    record['pid'] = child.pid
    (P / 'mono18-solve1-record.json').write_text(json.dumps(record, indent=2) + '\n')
    interrupted_at = None
    terminated = killed = False
    while child.poll() is None:
        if interrupted_at is None:
            reason = 'STOP' if stop.exists() or (P / 'STOP').exists() else 'disk-reserve' if shutil.disk_usage(P).free < 11 * 1024**3 // 2 else None
            if reason:
                record['cancellation_reason'] = reason
                record['cancellation_utc'] = datetime.now(timezone.utc).isoformat()
                interrupted_at = time.monotonic()
                child.send_signal(signal.SIGINT)
        elif time.monotonic() - interrupted_at > 20 and not killed:
            child.kill()
            killed = True
        elif time.monotonic() - interrupted_at > 10 and not terminated:
            child.terminate()
            terminated = True
        time.sleep(1)
    record['exit_code'] = child.returncode
record['finished_utc'] = datetime.now(timezone.utc).isoformat()
record['proof_bytes'] = prefix.with_suffix('.lrat').stat().st_size if prefix.with_suffix('.lrat').exists() else 0
(P / 'mono18-solve1-record.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record), flush=True)
if record['exit_code'] == 10 and 'cancellation_reason' not in record:
    rows = json.loads((P / 'cofactor-boundary11.json').read_text())
    _, ix, _ = enc2_base.make(11, 18, rows, True)
    positive = {int(v) for line in prefix.with_suffix('.stdout').read_text().splitlines() if line.startswith('v ') for v in line[2:].split() if int(v) > 0}
    gates = []
    for j in range(18):
        op = next(k for k in range(3) if ix(0, j, k) in positive)
        a = next(k for k in range(12 + j) if ix(1, j, k) in positive)
        b = next(k for k in range(12 + j) if ix(2, j, k) in positive)
        gates.append([3 if op == 2 else op, 100000 if a == 11 + j else a, 100000 if b == 11 + j else b])
    out = next(k for k in range(30) if ix(6, 0, k) in positive)
    c = {'physical_inputs': 11, 'input_map': list(range(10)), 'free_unary': 'not', 'gates': gates,
         'output': 100000 if out == 29 else out}
    path = P / 'mono18-solve1.circuit.json'
    path.write_text(json.dumps(c, indent=2) + '\n')
    checked = validate.check(path)
    (P / 'mono18-solve1-fullcheck.json').write_text(json.dumps(checked, indent=2) + '\n')
    print('SAT model full1024 wrong rows:', checked['wrong_rows'], 'counterexample:', checked['is_posted_counterexample'], flush=True)
