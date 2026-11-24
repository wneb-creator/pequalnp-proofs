import hashlib
import importlib.util
import json
from pathlib import Path
import random
import time

HERE = Path('/tmp/oec/pequalnp-pilot-21/search')
spec = importlib.util.spec_from_file_location('abnormal_tested', HERE/'cegis-abnormal-or-sinks-stream.py')
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
ops = [c.var() for _ in range(38)]
own_atoms = [c.var() for _ in range(13)]
own = [v if j % 2 else -v for j, v in enumerate(own_atoms)]
supports = [[c.var() for _ in range(13)] for _ in range(38)]
before = c.n
threshold = q.abnormal_partition(c, ops, {'own_complement': own}, supports)
rng = random.Random(10240813)
started = time.monotonic()
accepted = rejected = 0
for trial in range(400):
    ands = set(rng.sample(range(38), trial % 39))
    abnormal = set(rng.sample(range(13), trial % 14))
    masks = [rng.randrange(8192) for _ in supports]
    for w in abnormal:
        masks[25+w] = 8191
    break_support = trial % 3 == 0 and bool(abnormal)
    if break_support:
        masks[25+min(abnormal)] ^= 1 << (trial % 13)
    assumptions = [v if j in ands else -v for j, v in enumerate(ops)]
    assumptions.extend(literal if w in abnormal else -literal for w, literal in enumerate(own))
    for mask, row in zip(masks, supports):
        assumptions.extend(v if mask >> p & 1 else -v for p, v in enumerate(row))
    expected = len(ands) >= 8 and bool(abnormal) and not break_support
    model = propagate(c.cs, assumptions)
    assert (model is not None) == expected
    if model is not None:
        accepted += 1
        assert len(model) == c.n and model[threshold]
        assert all(any(model[abs(x)] == (x > 0) for x in clause) for clause in c.cs)
    else:
        rejected += 1
assert accepted > 0 and rejected > 0
result = {'status': 'PASS', 'integrated_fixed_cases': 400,
          'accepted': accepted, 'rejected': rejected,
          'threshold_auxiliary_variables': c.n-before, 'integrated_partition_clauses': len(c.cs),
          'signed_own_complement_literals_checked': True,
          'cases_include': ['fewer than eight ANDs', 'no abnormal output', 'missing abnormal support point', 'valid guards'],
          'source_sha256': hashlib.sha256((HERE/'cegis-abnormal-or-sinks-stream.py').read_bytes()).hexdigest(),
          'elapsed_seconds': time.monotonic()-started}
(HERE/'abnormal-partition-test.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
