import hashlib
import importlib.util
import json
from pathlib import Path
import random
import time

HERE = Path('/tmp/oec/pequalnp-pilot-21/search')
spec = importlib.util.spec_from_file_location('supported_tested', HERE/'cegis-disconnected-five-supported.py')
q = importlib.util.module_from_spec(spec)
spec.loader.exec_module(q)


class CNF:
    def __init__(self):
        self.n = 0
        self.cs = []
    def var(self):
        self.n += 1
        return self.n
    def add(self, *xs):
        self.cs.append(tuple(xs))


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


c = CNF()
labels = [[c.var() for _ in range(13)] for _ in range(5)]
lows = {v: [c.var() for _ in range(20)] for v in q.LOW_LABELS}
supports = [[c.var() for _ in range(13)] for _ in range(14)]
before = c.n
q.parent_support_guards(c, labels, lows, supports)
rng = random.Random(10245331)
started = time.monotonic()
accepted = 0
rejected = 0
for trial in range(400):
    ids = [0, 1]+rng.sample(list(range(2, 13)), 3)
    required = {v: set() for v in list(range(4))+q.LOW_LABELS}
    for vertex in required:
        for e, edge in enumerate(q.EDGES):
            if vertex not in edge:
                continue
            neighbour = next(v for v in edge if v != vertex)
            for other, second in enumerate(q.EDGES):
                if other != e and neighbour in second:
                    required[vertex] |= set(q.f.LINES[ids[e]])-set(q.f.LINES[ids[other]])
    masks = [{p for p in range(13) if rng.getrandbits(1)} for _ in supports]
    for v in range(4):
        masks[5+v] |= required[v]
    mode = trial % 4
    if mode == 0:
        choices = {4: 15, 5: 16, 8: 17}
    elif mode == 1:
        choices = {4: 15, 5: 15, 8: 15}
    elif mode == 2:
        choices = {v: rng.randrange(20) for v in q.LOW_LABELS}
    else:
        choices = {4: 15, 5: 16, 8: 13+((trial // 4) % 2)}
    for v, source in choices.items():
        if source >= 15:
            masks[source-15] |= required[v]
    if trial % 5 == 0:
        victim = trial % 4
        masks[5+victim].discard(min(required[victim]))
    actual = {v: masks[5+v] for v in range(4)}
    for v, source in choices.items():
        actual[v] = {source} if source < 13 else set() if source < 15 else masks[source-15]
    expected = all(required[v] <= actual[v] for v in required)
    assumptions = []
    for j, row in enumerate(labels):
        assumptions.extend(value if w == ids[j] else -value for w, value in enumerate(row))
    for v, row in lows.items():
        assumptions.extend(value if k == choices[v] else -value for k, value in enumerate(row))
    for mask, row in zip(masks, supports):
        assumptions.extend(value if p in mask else -value for p, value in enumerate(row))
    model = propagate(c.cs, assumptions)
    assert (model is not None) == expected
    if model is not None:
        accepted += 1
        assert len(model) == c.n
        assert all(any(model[abs(x)] == (x > 0) for x in clause) for clause in c.cs)
    else:
        rejected += 1
assert accepted > 0 and rejected > 0
result = {'status': 'PASS', 'fixed_label_support_models': 400,
          'accepted': accepted, 'rejected': rejected,
          'additional_support_variables': c.n-before, 'clauses': len(c.cs),
          'cases_include': ['coalesced low selectors', 'raw low selectors', 'false/true constants', 'generated low selectors'],
          'source_sha256': hashlib.sha256((HERE/'cegis-disconnected-five-supported.py').read_bytes()).hexdigest(),
          'elapsed_seconds': time.monotonic()-started}
(HERE/'disconnected-support-test.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
