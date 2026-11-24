import hashlib
import importlib.util
import json
from pathlib import Path
import random
import time

HERE = Path('/tmp/oec/pequalnp-pilot-21/search')
spec = importlib.util.spec_from_file_location('disconnected_tested', HERE/'cegis-disconnected-five.py')
q = importlib.util.module_from_spec(spec)
spec.loader.exec_module(q)


class CNF:
    def __init__(self):
        self.n = 0
        self.cs = []
    def var(self):
        self.n += 1
        return self.n
    def add(self, *literals):
        self.cs.append(tuple(literals))


def propagate(clauses, assumptions):
    values = {abs(x): x > 0 for x in assumptions}
    changed = True
    while changed:
        changed = False
        for clause in clauses:
            pending = []
            satisfied = False
            for x in clause:
                if abs(x) not in values:
                    pending.append(x)
                elif values[abs(x)] == (x > 0):
                    satisfied = True
                    break
            if satisfied:
                continue
            if not pending:
                return None
            if len(pending) == 1:
                x = pending[0]
                values[abs(x)] = x > 0
                changed = True
    return values


def encoded_values(gates, mask):
    wires = [bool(mask >> p & 1) for p in range(13)] + [False, True]
    for a, b, op in gates:
        wires.append(wires[a] and wires[b] if op else wires[a] or wires[b])
    return wires


started = time.monotonic()
rng = random.Random(1024533)
checked = 0
row_cases = 0
rejected_constant_models = 0
while checked < 64:
    gates = [(0, 13, True), (1, 14, False), (2, 14, True), (3, 13, False), (17, 17, True)]
    for j in range(5, 14):
        a = rng.randrange(15+j) if j < 9 else rng.randrange(13)
        b = rng.randrange(15+j)
        a, b = sorted((a, b))
        gates.append((a, b, bool(rng.getrandbits(1)) if j < 9 else False))
    try:
        result = q.rebuild(gates, list(range(5)))
    except AssertionError as error:
        assert 'cannot be constant' in str(error)
        rejected_constant_models += 1
        continue
    for mask in range(8192):
        original = encoded_values(gates, mask)
        rebuilt = [bool(mask >> p & 1) for p in range(13)]
        for a, b, op in result['gates']:
            assert 0 <= a < len(rebuilt) and 0 <= b < len(rebuilt)
            rebuilt.append(rebuilt[a] and rebuilt[b] if op else rebuilt[a] or rebuilt[b])
        for w in range(13):
            wanted = original[24+w] if w < 5 else any(mask >> p & 1 for p in q.f.LINES[w])
            assert rebuilt[result['out'][w]] == wanted
    if checked < 8:
        c = CNF()
        ops, aa, bb, assumptions = [], [], [], []
        for j, (a, b, op) in enumerate(gates):
            flag = c.var()
            ops.append(flag)
            assumptions.append(flag if op else -flag)
            aa.append([c.var() for _ in range(15+j)])
            bb.append([c.var() for _ in range(15+j)])
            assumptions.extend(v if k == a else -v for k, v in enumerate(aa[-1]))
            assumptions.extend(v if k == b else -v for k, v in enumerate(bb[-1]))
        masks = [0, 8191]+rng.sample(range(8192), 16)
        rows = {mask: q.row_values(c, ops, aa, bb, mask) for mask in masks}
        model = propagate(c.cs, assumptions)
        assert model is not None and len(model) == c.n
        for mask, values in rows.items():
            wanted = encoded_values(gates, mask)[15:]
            assert [model[v] for v in values] == wanted
            wrong = -values[-1] if wanted[-1] else values[-1]
            assert propagate(c.cs, assumptions+[wrong]) is None
            row_cases += 1
    checked += 1

maps = json.loads((HERE/'line-pair-maps.json').read_text())
assert set(maps) == {f'{a},{b}' for a in range(13) for b in range(13) if a != b}
lines = [frozenset(line) for line in q.f.LINES]
for key, perm in maps.items():
    a, b = map(int, key.split(','))
    assert sorted(perm) == list(range(13))
    assert {frozenset(perm[p] for p in line) for line in lines} == set(lines)
    assert frozenset(perm[p] for p in lines[a]) == lines[0]
    assert frozenset(perm[p] for p in lines[b]) == lines[1]
result = {'status': 'PASS', 'constant_copy_rebuild_networks': checked,
          'rebuild_input_rows_each': 8192, 'fixed_network_CNF_rows': row_cases,
          'constant_output_models_rejected': rejected_constant_models,
          'ordered_line_pair_maps_checked': len(maps),
          'source_sha256': hashlib.sha256((HERE/'cegis-disconnected-five.py').read_bytes()).hexdigest(),
          'elapsed_seconds': time.monotonic()-started}
(HERE/'disconnected-five-test.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
