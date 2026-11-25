import argparse
import json
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('--q', type=int, default=5)
ap.add_argument('--out', required=True)
args = ap.parse_args()
q = args.q
N = q*q + q + 1
n = 2*N
gates = []

def gate(op, a, b):
    assert 0 <= a < n + len(gates) and 0 <= b < n + len(gates)
    gates.append((op, a, b))
    return n + len(gates) - 1

def disj(ws):
    ws = list(ws)
    assert ws
    acc = ws[0]
    for w in ws[1:]:
        acc = gate('or', acc, w)
    return acc

X = [disj(a*q+b for b in range(q)) for a in range(q)]
Y = [disj(a*q+b for a in range(q)) for b in range(q)]
M = [disj(N+a*q+b for b in range(q)) for a in range(q)]
B = [disj(N+a*q+b for a in range(q)) for b in range(q)]
product = [disj(gate('and', X[a], M[b]) for a in range(q) for b in range(q)
    if a*b % q == k) for k in range(q)]
summation = [disj(gate('and', product[a], B[b]) for a in range(q) for b in range(q)
    if (a+b) % q == k) for k in range(q)]
affine = disj(gate('and', summation[a], Y[a]) for a in range(q))
vertical = disj(gate('and', X[a], N+q*q+a) for a in range(q))
slopes = disj(gate('and', q*q+a, M[a]) for a in range(q))
infinity = gate('and', disj(q*q+a for a in range(q+1)), N+q*q+q)
vertical_infinity = gate('and', q*q+q, disj(N+q*q+a for a in range(q)))
output = disj([affine, vertical, slopes, infinity, vertical_infinity])

def incident(p, l):
    if p < q*q:
        x, y = divmod(p, q)
        if l < q*q:
            m, b = divmod(l, q)
            return y == (m*x+b) % q
        return l < q*q+q and x == l-q*q
    if p < q*q+q:
        return l == q*q+q or (l < q*q and l//q == p-q*q)
    return l >= q*q

def evaluate(mask):
    wires = [bool(mask >> i & 1) for i in range(n)]
    for op, a, b in gates:
        wires.append(wires[a] and wires[b] if op == 'and' else wires[a] or wires[b])
    return wires[output]

def graph(mask):
    return any(mask >> p & 1 and mask >> (N+l) & 1 and incident(p, l)
        for p in range(N) for l in range(N))

assert len(gates) == 8*q*q+2*q+2
assert all(sum(incident(p, l) for p in range(N)) == q+1 for l in range(N))
assert all(sum(incident(p, l) and incident(r, l) for l in range(N)) == 1
    for p in range(N) for r in range(p))
assert not evaluate(0)
for u in range(n):
    for v in range(u, n):
        mask = (1 << u) | (1 << v)
        assert evaluate(mask) == graph(mask), (u, v)
witness = [q, N+1, N+q]
mask = sum(1 << i for i in witness)
assert evaluate(mask) and not graph(mask)
out = dict(q=q, N=N, n=n, gates=gates, output=output,
    canonical=N*(q+2)-1, size=len(gates), false_positive=witness,
    pairs_checked=n*(n+1)//2,
    incidence=[[p,l] for p in range(N) for l in range(N) if incident(p,l)])
Path(args.out).write_text(json.dumps(out))
print(json.dumps({k:v for k,v in out.items() if k not in ('gates', 'incidence')}))
