import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import resource
import time

HERE = Path('/tmp/oec/pequalnp-pilot-21/search')
spec = importlib.util.spec_from_file_location('general_tested', HERE/'cegis-general-five.py')
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


c = CNF()
ops = [c.var() for _ in range(14)]
aa = [[c.var() for _ in range(15+j)] for j in range(14)]
bb = [[c.var() for _ in range(15+j)] for j in range(14)]
q.general_root_guards(c, ops, aa, bb)
cases = []
for late in itertools.product((False, True), repeat=5):
    values = {v: False for v in range(1, c.n+1)}
    for j, is_late in enumerate(late):
        root = 9+j
        values[aa[root][0]] = True
        values[bb[root][21+j % 3 if is_late else 1]] = True
    got = all(any(values[abs(x)] == (x > 0) for x in clause) for clause in c.cs)
    assert got == (sum(late) >= 4)
    cases.append(got)
for root in range(10, 14):
    values = {v: False for v in range(1, c.n+1)}
    for j in range(9, 14):
        values[aa[j][0]] = True
        values[bb[j][21]] = True
    values[aa[root][0]] = False
    values[aa[root][24]] = True
    assert not all(any(values[abs(x)] == (x > 0) for x in clause) for clause in c.cs)
for root in range(9, 14):
    values = {v: False for v in range(1, c.n+1)}
    for j in range(9, 14):
        values[aa[j][0]] = True
        values[bb[j][21]] = True
    values[ops[root]] = True
    assert not all(any(values[abs(x)] == (x > 0) for x in clause) for clause in c.cs)


class CountOnly(q.f.b.CNF):
    def __init__(self):
        self.n = 0
        self.clauses = 0
        self.body_bytes = 0
    def add(self, *xs):
        self.clauses += 1
        self.body_bytes += len(' '.join(map(str, xs)))+3


started = time.monotonic()
count = CountOnly()
q.encode(count, q.f.ROWS)
size = count.body_bytes+len(f'p cnf {count.n} {count.clauses}\n')
result = {'status': 'PASS', 'last_three_truth_patterns': len(cases),
          'patterns_accepted': sum(cases), 'earlier_output_rejections': 4,
          'AND_root_rejections': 5, 'count_only_no_CNF_or_solver': True,
          'variables': count.n, 'clauses': count.clauses, 'exact_DIMACS_bytes': size,
          'band_rows': len(q.f.ROWS), 'elapsed_seconds': time.monotonic()-started,
          'max_RSS_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
          'source_sha256': hashlib.sha256((HERE/'cegis-general-five.py').read_bytes()).hexdigest()}
(HERE/'general-five-test-count.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
