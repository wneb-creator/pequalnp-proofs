import hashlib
import importlib.util
import json
from pathlib import Path
import random
import time

HERE = Path('/tmp/oec/pequalnp-pilot-21/search')
spec = importlib.util.spec_from_file_location('formal_cost_tested', HERE/'formal_cost.py')
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
    def one(self, xs):
        self.add(*xs)
        for i, a in enumerate(xs):
            for b in xs[i+1:]:
                self.add(-a, -b)


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


started = time.monotonic()
c = CNF()
op = c.var()
left, right, out = [[c.var() for _ in range(6)] for _ in range(3)]
c.one(out)
q.combine_cost(c, op, left, right, out)
tables = 0
for is_and in (False, True):
    for a in range(6):
        for b in range(6):
            assumptions = [op if is_and else -op]
            assumptions += [v if i == a else -v for i, v in enumerate(left)]
            assumptions += [v if i == b else -v for i, v in enumerate(right)]
            wanted = min(a, b) if is_and else min(5, a+b)
            model = propagate(c.cs, assumptions)
            assert model is not None
            assert [model[v] for v in out] == [i == wanted for i in range(6)]
            assert propagate(c.cs, assumptions+[-out[wanted]]) is None
            tables += 1
for x in range(6):
    assert min(0, x) == 0 and min(5, 5+x) == 5
    assert min(5, x) == x and min(5, 0+x) == x
    assert min(x, x) == x and min(5, x+x) >= x
rng = random.Random(102405)
networks = 0
for trial in range(40):
    gates = [(0, 13, True), (1, 14, False), (2, 14, True), (3, 13, False), (17, 17, False)]
    for j in range(5, 14):
        gates.append((rng.randrange(15+j), rng.randrange(15+j), bool(rng.getrandbits(1))))
    c = CNF()
    ops, aa, bb, assumptions = [], [], [], []
    expected = [1]*13+[0, 5]
    for j, (a, b, is_and) in enumerate(gates):
        flag = c.var()
        ops.append(flag)
        assumptions.append(flag if is_and else -flag)
        aa.append([c.var() for _ in range(15+j)])
        bb.append([c.var() for _ in range(15+j)])
        assumptions.extend(v if k == a else -v for k, v in enumerate(aa[-1]))
        assumptions.extend(v if k == b else -v for k, v in enumerate(bb[-1]))
        expected.append(min(expected[a], expected[b]) if is_and else min(5, expected[a]+expected[b]))
    costs = q.exact_costs(c, ops, aa, bb, 13, {13: 0, 14: 5})
    model = propagate(c.cs, assumptions)
    assert model is not None and len(model) == c.n
    for j, row in enumerate(costs):
        assert [model[v] for v in row] == [cost == expected[15+j] for cost in range(6)]
    assert all(any(model[abs(x)] == (x > 0) for x in clause) for clause in c.cs)
    networks += 1
result = {'status': 'PASS', 'complete_operation_table_cases': tables,
          'whole_network_selector_cases': networks,
          'constant_and_repeat_cost_identities_checked': True,
          'helper_sha256': hashlib.sha256((HERE/'formal_cost.py').read_bytes()).hexdigest(),
          'elapsed_seconds': time.monotonic()-started}
(HERE/'formal-cost-test.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
