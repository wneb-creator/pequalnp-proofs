import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random
import time

HERE = Path('/tmp/oec/pequalnp-pilot-21/search')
spec = importlib.util.spec_from_file_location('guarded', HERE/'guarded_and_count.py')
guarded = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guarded)

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
    values = {}
    for literal in assumptions:
        v, truth = abs(literal), literal > 0
        if v in values and values[v] != truth:
            return None
        values[v] = truth
    changed = True
    while changed:
        changed = False
        for clause in clauses:
            unassigned = []
            satisfied = False
            for literal in clause:
                v = abs(literal)
                if v not in values:
                    unassigned.append(literal)
                elif values[v] == (literal > 0):
                    satisfied = True
                    break
            if satisfied:
                continue
            if not unassigned:
                return None
            if len(unassigned) == 1:
                literal = unassigned[0]
                values[abs(literal)] = literal > 0
                changed = True
    return values

started = time.monotonic()
checked = 0
for n in range(1, 9):
    for minimum in range(1, n+1):
        c = CNF()
        raw = [c.var() for _ in range(n)]
        literals = [v if j % 2 else -v for j, v in enumerate(raw)]
        threshold = guarded.at_least(c, literals, minimum)
        for bits in itertools.product((False, True), repeat=n):
            assumptions = [v if truth else -v for v, truth in zip(raw, bits)]
            count = sum(truth == (literal > 0) for truth, literal in zip(bits, literals))
            expected = count >= minimum
            model = propagate(c.cs, assumptions)
            assert model is not None and len(model) == c.n
            assert model[threshold] == expected
            assert propagate(c.cs, assumptions+[-threshold if expected else threshold]) is None
            assert all(any(model[abs(x)] == (x > 0) for x in clause) for clause in c.cs)
            checked += 1
rng = random.Random(1024)
c = CNF()
raw = [c.var() for _ in range(38)]
original_ands = [-v for v in raw]
own = [c.var() for _ in range(13)]
threshold = guarded.abnormal_needs_eight_ands(c, original_ands, own)
for trial in range(256):
    count = trial % 39
    chosen = set(rng.sample(range(38), count))
    op_assumptions = [-v if j in chosen else v for j,v in enumerate(raw)]
    for abnormal in (False, True):
        flags = [-v for v in own]
        if abnormal:
            flags[trial % 13] *= -1
        model = propagate(c.cs, op_assumptions+flags)
        assert (model is not None) == (not abnormal or count >= 8)
        if model is not None:
            assert len(model) == c.n
            assert model[threshold] == (count >= 8)
            assert all(any(model[abs(x)] == (x > 0) for x in clause) for clause in c.cs)
        checked += 1
result = {'status':'PASS','complete_threshold_assignments_and_guard_cases':checked,
          'full38_inputs_plus13_guards_variables':c.n,'full38_clauses':len(c.cs),
          'source_sha256':hashlib.sha256((HERE/'guarded_and_count.py').read_bytes()).hexdigest(),
          'elapsed_seconds':time.monotonic()-started}
(HERE/'guarded-and-count-test.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
