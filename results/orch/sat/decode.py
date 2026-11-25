import argparse
import json
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('model')
p.add_argument('output')
p.add_argument('--n', type=int, default=10)
p.add_argument('--s', type=int, default=19)
args = p.parse_args()
positive = set()
status = []
for line in Path(args.model).read_text().splitlines():
    if line.startswith('s '):
        status.append(line)
    elif line.startswith('v '):
        positive.update(v for v in map(int, line.split()[1:]) if v > 0)
if status != ['s SATISFIABLE']:
    raise SystemExit('Expected SAT model; got ' + repr(status))
n, s = args.n, args.s
A = 2**n + n + s + 2
ix = lambda kind, j, a: (kind * (s + 1) + j) * A + a + 1
gates = []
for j in range(s):
    op = [a for a in range(4) if ix(0, j, a) in positive]
    a = [k for k in range(n + j + 1) if ix(1, j, k) in positive]
    b = [k for k in range(n + j + 1) if ix(2, j, k) in positive]
    assert len(op) == len(a) == len(b) == 1, (j, op, a, b)
    gates.append((op[0], a[0], b[0]))
outs = [k for k in range(n + s + 1) if ix(6, 0, k) in positive]
assert outs, 'No output selector'
output = outs[0]
edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
wrong = []
for row in range(2**n):
    w = [bool(row >> i & 1) for i in range(n)]
    get = lambda i: w[i] if i < len(w) else False
    for op,a,b in gates:
        w.append((get(a) and get(b)) if op == 0 else
                 (get(a) or get(b)) if op == 1 else
                 True if op == 2 else not get(a))
    value = get(output)
    goal = any((row >> u & 1) and (row >> v & 1) for u,v in edges)
    if value != goal:
        wrong.append(row)
record = {'n':n,'gates':gates,'output':output,'not_count':sum(op==3 for op,a,b in gates),'wrong':wrong}
Path(args.output).write_text(json.dumps(record,indent=2)+'\n')
print('NOT:',record['not_count'],'wrong rows:',len(wrong),'output:',output)
print('gates:',gates)
print('wrong:',wrong)
