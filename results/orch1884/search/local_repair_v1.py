import argparse, itertools, json, os, signal, subprocess, time
from datetime import datetime, timezone
from pathlib import Path

P = argparse.ArgumentParser()
P.add_argument('--seed', required=True)
P.add_argument('--seconds', type=int, default=110)
P.add_argument('--max-nots', type=int, default=0)
P.add_argument('--tag', default='repair')
args = P.parse_args()
root = Path('/tmp/oec/pequalnp-pilot-103/orch1884')
script = root / 'free_not_cnf.py'
data = json.loads(Path(args.seed).read_text())
gates = data['gates'] if isinstance(data, dict) else data
assert len(gates) == 18
seed = root / f'{args.tag}-frozen-seed.json'
seed.write_text(json.dumps(gates) + '\n')
priority = {2, 6, 14}
groups = sorted(itertools.combinations(range(18), 3),
                key=lambda g: (-len(set(g) & priority), sum(abs(i-j) for i in g for j in priority), g))
start = time.monotonic()
deadline = start + args.seconds
records = []
pidfile = root / f'{args.tag}-running.json'
print('START', datetime.now(timezone.utc).isoformat(), vars(args), flush=True)
for index, group in enumerate(groups):
    if time.monotonic() >= deadline - 1:
        break
    tag = f'{args.tag}-case{index:03d}'
    command = ['python3', str(script), '--gates', '18', '--max-nots', str(args.max_nots),
               '--seconds', '2', '--allow-unused', '--pin', str(seed),
               '--mutable', ','.join(map(str, group)), '--tag', tag]
    log = root / f'{tag}.log'
    with log.open('w') as out:
        proc = subprocess.Popen(command, stdout=out, stderr=subprocess.STDOUT, start_new_session=True)
        pidfile.write_text(json.dumps({'driver_pid': os.getpid(), 'case_pid': proc.pid,
                                     'case_tag': tag, 'started': datetime.now(timezone.utc).isoformat()}) + '\n')
        try:
            proc.wait(timeout=min(3, max(.05, deadline - time.monotonic())))
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGTERM)
            proc.wait()
    result = root / f'{tag}-result.json'
    entry = {'index': index, 'mutable': group, 'exit': proc.returncode}
    if result.exists():
        d = json.loads(result.read_text())
        entry['stages'] = [{k: v for k, v in stage.items() if k not in ['candidate', 'bad_rows']}
                           for stage in d['stages']]
        entry['status'] = d['stages'][-1]['status'] if d['stages'] else 'UNKNOWN'
        entry['candidate_validated'] = bool(d['stages'] and d['stages'][-1].get('bad_rows') == [])
    else:
        entry['status'] = 'UNKNOWN'
        entry['candidate_validated'] = False
    records.append(entry)
    for cnf in root.glob(f'{tag}-stage*.cnf'):
        cnf.unlink()
    print('CASE', json.dumps(entry, sort_keys=True), flush=True)
    (root / f'{args.tag}-report.json').write_text(json.dumps({
        'seed': str(seed), 'elapsed_seconds': time.monotonic() - start,
        'completed': len(records), 'total_three_gate_neighborhoods': len(groups),
        'max_paid_nots': args.max_nots, 'cases': records,
        'complete_neighborhood_census': len(records) == len(groups),
        'all_other_gate_definitions_pinned': True,
        'global_lower_bound_proved': False}, indent=2) + '\n')
    if entry['candidate_validated']:
        print('WITNESS_CASE', tag, flush=True)
        break
pidfile.write_text(json.dumps({'driver_pid': None, 'case_pid': None, 'finished': True}) + '\n')
print('FINISHED', len(records), 'elapsed', time.monotonic() - start, flush=True)
