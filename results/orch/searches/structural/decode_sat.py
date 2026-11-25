import importlib.util
import json
import sys
from pathlib import Path

stem = sys.argv[1]
d = json.loads(Path(stem + '.json').read_text())
solution = Path(stem + '.sol').read_text().splitlines()
if not any(line == 's SATISFIABLE' for line in solution):
    print(json.dumps({'status': [line for line in solution if line.startswith('s ')]}))
    raise SystemExit(0)
assignment = {}
for line in solution:
    if line.startswith('v '):
        for x in map(int, line.split()[1:]):
            if x:
                assignment[abs(x)] = x > 0
for line in Path(stem + '.cnf').read_text().splitlines():
    if line.startswith(('c', 'p')):
        continue
    xs = list(map(int, line.split()))[:-1]
    assert any(assignment[abs(x)] == (x > 0) for x in xs), xs
gates = []
for op, selectors in zip(d['ops'], d['selectors']):
    inputs = [[i for i, v in enumerate(port) if assignment[v]] for port in selectors]
    assert all(len(x) == 1 for x in inputs)
    gates.append((int(assignment[op]), inputs[0][0], inputs[1][0]))
spec = importlib.util.spec_from_file_location('core_evaluator',
    '/tmp/oec/pequalnp-pilot-71/core-counterexample/evaluator.py')
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
model = mod.Model(d['n'], 7, d['edges'], 'Fano SAT independent verification')
analysis = model.analyze(gates)
cover = [i for i, v in enumerate(d['cover']) if assignment[v]]
accepted_vars = d.get('accepts', d['vals'][-1][len(d['independent']):])
accepted = [edge for edge, v in zip(d['edges'], accepted_vars)
            if assignment[v]]
assert all(a in cover or b in cover for a, b in d['edges'] if [a, b] not in accepted)
if d['violation']:
    assert len(accepted) + 7 > len(gates) + d.get('roots', 1) + len(cover)
    assert analysis is not None and analysis[0] < 0, analysis
if d.get('core', False):
    assert analysis is not None and analysis[3] == d.get('roots', 1), analysis
out = dict(status='SAT verified', gates=gates, accepted=accepted, cover=cover,
           independent_analysis=analysis)
Path(stem + '-decoded.json').write_text(json.dumps(out, indent=2))
print(json.dumps(out, indent=2))
