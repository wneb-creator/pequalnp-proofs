import argparse
import hashlib
import json
import resource
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--name', required=True)
parser.add_argument('--cnf', type=Path, required=True)
parser.add_argument('--seconds', type=int, required=True)
parser.add_argument('--preset', choices=('default', 'sat', 'unsat'), default='default')
parser.add_argument('--seed', type=int, default=1)
args = parser.parse_args()
assert args.seconds > 0 and args.seed >= 0
base = Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
cnf = args.cnf.resolve()
solver = base / 'kissat/build/kissat'
command = [str(solver), '-s', f'--time={args.seconds}', f'--seed={args.seed}']
if args.preset != 'default':
    command.append(f'--{args.preset}')
command.append(str(cnf))
def stamp():
    return datetime.now(timezone.utc).isoformat()
meta = {'name': args.name, 'started_at': stamp(), 'wall_limit_seconds': args.seconds,
        'command': command, 'backend': 'kissat', 'preset': args.preset, 'verification': 'all underlying correlated inputs and all16384 full inputs',
        'cnf_sha256': hashlib.sha256(cnf.read_bytes()).hexdigest(),
        'solver_sha256': hashlib.sha256(solver.read_bytes()).hexdigest()}
runpath = base / f'{args.name}-run.json'
assert not runpath.exists()
runpath.write_text(json.dumps(meta, indent=2))
before = resource.getrusage(resource.RUSAGE_CHILDREN)
start = time.monotonic()
solve_log = base / f'{args.name}-solve.log'
with solve_log.open('w') as log:
    rc = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT).returncode
after = resource.getrusage(resource.RUSAGE_CHILDREN)
result = {**meta, 'finished_at': stamp(), 'wall_seconds': time.monotonic() - start,
          'cpu_seconds': after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime,
          'max_rss_kib': after.ru_maxrss, 'exit_code': rc,
          'status': {0: 'UNKNOWN', 10: 'SAT', 20: 'UNSAT'}.get(rc, 'ERROR')}
if rc == 10:
    verify = base / f'{args.name}-verified.log'
    with verify.open('w') as log:
        checked = subprocess.run([sys.executable, str(base / 'decode_correlated_family.py'),
                                  str(cnf.with_suffix('.map.json')), str(solve_log)],
                                 stdout=log, stderr=subprocess.STDOUT)
    result['full_truth_table_verified'] = checked.returncode == 0
    if checked.returncode == 0:
        text = verify.read_text()
        gates, _ = json.JSONDecoder().raw_decode(text.split('\n', 1)[1])
        witness = base / f'{args.name}-witness.json'
        witness.write_text(json.dumps(gates, indent=2))
        result['witness_file'] = str(witness)
(base / f'{args.name}-result.json').write_text(json.dumps(result, indent=2))
print(json.dumps(result), flush=True)
