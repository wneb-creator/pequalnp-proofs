import json, math, random, time
from pathlib import Path

# Heuristic only: look for a full bipartite quadratic Boolean function with
# a diagonal fooling set of size four, computed with only three AND gates.
# OR gates are free and represented by arbitrary subsets of prior wires.
n = 8
k = 3
full = (1 << (1 << n)) - 1
variables = [sum(1 << x for x in range(1 << n) if x >> i & 1) for i in range(n)]
orvars = [0] * (1 << n)
for mask in range(1, 1 << n):
    bit = mask & -mask
    orvars[mask] = orvars[mask ^ bit] | variables[bit.bit_length() - 1]
edge_tables = [variables[i] & variables[4+j] for i in range(4) for j in range(4)]
edge_inputs = [(1 << i) | (1 << (4+j)) for i in range(4) for j in range(4)]
graph_tables = [0] * (1 << 16)
for mask in range(1, 1 << 16):
    bit = mask & -mask
    graph_tables[mask] = graph_tables[mask ^ bit] | edge_tables[bit.bit_length() - 1]

def evaluate(circuit):
    gates = []
    for i in range(k):
        sides = []
        for mask in circuit[2*i:2*i+2]:
            value = orvars[mask & 255]
            for j in range(i):
                if mask >> (8+j) & 1:
                    value |= gates[j]
            sides.append(value)
        gates.append(sides[0] & sides[1])
    out = 0
    for j in range(k):
        if circuit[-1] >> j & 1:
            out |= gates[j]
    edges = sum(((out >> index) & 1) << i for i,index in enumerate(edge_inputs))
    missing = sum(not (edges >> (5*i) & 1) for i in range(4))
    collisions = sum(bool(edges >> (4*i+j) & 1) and bool(edges >> (4*j+i) & 1)
                     for i in range(4) for j in range(i))
    residual = (out & ~graph_tables[edges]).bit_count()
    return 30*missing + 20*collisions + residual, edges, residual

random.seed(2602)
started = time.monotonic()
best = 10000
trials = 0
for restart in range(1000):
    c = [random.randrange(1 << (n+i)) for i in range(k) for _ in range(2)] + [random.randrange(1,8)]
    score, edges, residual = evaluate(c)
    for step in range(2000):
        trials += 1
        j = random.randrange(7)
        width = 3 if j == 6 else 8 + j//2
        old = c[j]
        c[j] ^= 1 << random.randrange(width)
        score2, edges2, residual2 = evaluate(c)
        temperature = 0.35 + 6 * (1-step/2000)**2
        if score2 <= score or random.random() < math.exp((score-score2)/temperature):
            score, edges, residual = score2, edges2, residual2
        else:
            c[j] = old
        if score < best:
            best = score
            result = dict(score=score, edges=edges, residual=residual, circuit=c.copy(),
                          trials=trials, elapsed=time.monotonic()-started)
            print(json.dumps(result), flush=True)
            Path('/tmp/oec/pequalnp-pilot-60/and-fooling-search-best.json').write_text(json.dumps(result,indent=2))
        if score == 0:
            raise SystemExit(0)
print(json.dumps(dict(best=best,trials=trials,elapsed=time.monotonic()-started)),flush=True)
