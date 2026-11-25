import itertools
import json
from pathlib import Path
import subprocess
import time

OUT = Path('/tmp/oec/pequalnp-pilot-66')
PAIRS = list(itertools.combinations(range(5), 2))
INDEX = {pair: i for i, pair in enumerate(PAIRS)}
PERMS = list(itertools.permutations(range(5)))
REPS = []
SEEN = set()
for mask in range(1 << len(PAIRS)):
    if mask in SEEN:
        continue
    edges = [pair for i, pair in enumerate(PAIRS) if mask >> i & 1]
    for perm in PERMS:
        translated = sum(1 << INDEX[tuple(sorted((perm[a], perm[b])))] for a, b in edges)
        SEEN.add(translated)
    REPS.append((mask, edges))
assert len(REPS) == 34


def solve(mask, edges, k, owned=False):
    label = f'alg5_{mask}_{k}' + ('_owned' if owned else '')
    fixture = OUT / f'alg5_graph_{mask}.json'
    fixture.write_text(json.dumps({'n': 5, 'edges': edges}))
    args = ['python3', str(OUT / 'circuit-sat.py'), '--graph', 'file:' + str(fixture),
            '--name', label, '--gates', str(k), '--seconds', '30']
    if owned:
        args.append('--all-owned')
    with (OUT / f'{label}.runlog').open('w') as log:
        result = subprocess.run(args, cwd='/workspace/pequalnp-proofs', stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError('SAT driver failed: ' + label)
    summary = json.loads((OUT / f'sat-{label}-{k}.json').read_text())
    if summary['returncode'] == 10:
        assert summary['all_inputs_validated']
    return summary


start = time.time()
results = []
for index, (mask, edges) in enumerate(REPS):
    used = set(v for edge in edges for v in edge)
    if not edges:
        results.append({'mask': mask, 'edges': edges, 'size': 0, 'all_owned': True, 'lower_unsat': True})
        continue
    cover = min(s.bit_count() for s in range(32) if all((s >> a & 1) or (s >> b & 1) for a, b in edges))
    upper = len(edges) + cover - 1
    lower_known = True
    entry = {'mask': mask, 'edges': edges, 'runs': []}
    for k in range(max(1, len(used) - 1), upper + 1):
        normal = solve(mask, edges, k)
        entry['runs'].append({'k': k, 'status': normal['returncode']})
        if normal['returncode'] == 20:
            continue
        if normal['returncode'] != 10:
            lower_known = False
            continue
        entry.update({'size': k, 'lower_unsat': lower_known, 'normal': normal})
        if all(item['edges'] for item in normal['ownership']):
            entry['all_owned'] = True
        else:
            owned = solve(mask, edges, k, True)
            entry['owned'] = owned
            entry['all_owned'] = owned['returncode'] == 10
            if owned['returncode'] == 20:
                entry['candidate_counterexample'] = True
        break
    results.append(entry)
    (OUT / 'alg-general5-results.json').write_text(json.dumps(results, indent=2))
    print(json.dumps({'index': index + 1, 'mask': mask, 'edges': len(edges),
                      'size': entry.get('size'), 'lower_unsat': entry.get('lower_unsat'),
                      'all_owned': entry.get('all_owned'),
                      'candidate_counterexample': entry.get('candidate_counterexample', False),
                      'elapsed': time.time() - start}), flush=True)
    if entry.get('candidate_counterexample'):
        break
print('DONE', len(results), 'graphs', time.time() - start, 'seconds', flush=True)
