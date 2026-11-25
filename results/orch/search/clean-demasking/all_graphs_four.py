import itertools, json, time

N = 4
MASK = (1 << (1 << N)) - 1
TRUTH = [sum(1 << s for s in range(1 << N) if s >> i & 1) for i in range(N)]
INITIAL = tuple(sorted(TRUTH[i] | (int(i == 1) << 16) | (int(i == 0) << 17) for i in range(N)))
EDGES = list(itertools.combinations(range(N), 2))
graphs = {}
for bits in range(1 << len(EDGES)):
    if not bits & 1:
        continue
    edges = [e for i, e in enumerate(EDGES) if bits >> i & 1]
    truth = sum(1 << s for s in range(1 << N) if any(s >> i & 1 and s >> j & 1 for i, j in edges))
    graphs[truth] = edges

def operate(a, b, op):
    if op == 0:
        return a | b
    av, bv = a & MASK, b & MASK
    d0 = ((av >> 1) & 1) & ((b >> 16) & 1) | ((a >> 16) & 1) & ((bv >> 1) & 1)
    d1 = ((av >> 2) & 1) & ((b >> 17) & 1) | ((a >> 17) & 1) & ((bv >> 2) & 1)
    return (av & bv) | (d0 << 16) | (d1 << 17)

def recover(state, final):
    avail = [TRUTH[i] | (int(i == 1) << 16) | (int(i == 0) << 17) for i in range(N)]
    remaining = list(state)
    for a in avail:
        remaining.remove(a)
    program = []
    while remaining:
        found = False
        for k, c in enumerate(remaining):
            for i, a in enumerate(avail):
                for j, b in enumerate(avail[:i]):
                    for op in [0, 1]:
                        if operate(a, b, op) == c:
                            program.append([op, i, j])
                            avail.append(c)
                            remaining.pop(k)
                            found = True
                            break
                    if found: break
                if found: break
            if found: break
        if not found:
            raise RuntimeError('unreachable semantic state')
    op, a, b = final
    ia = avail.index(a)
    ib = next(i for i, v in enumerate(avail) if v == b and i != ia)
    return program + [[op, ia, ib]]

ordinary = {}
double = {}
double_witness = {}
frontier = {INITIAL}
start = time.monotonic()
interned = {x: x for x in INITIAL}
for depth in range(1, 7):
    nxt = set()
    for state in frontier:
        counts = {x: state.count(x) for x in state}
        for i, a in enumerate(state):
            for b in state[:i]:
                for op in [0, 1]:
                    c = operate(a, b, op)
                    truth = c & MASK
                    if truth in graphs:
                        ordinary.setdefault(truth, depth)
                        if c >> 16 == 0 and truth not in double:
                            double[truth] = depth
                            double_witness[truth] = recover(state, (op, a, b))
                    if depth == 6:
                        continue
                    if counts.get(c, 0) >= 2:
                        continue
                    c = interned.setdefault(c, c)
                    nxt.add(tuple(sorted(state + (c,))))
    frontier = nxt
    print(json.dumps({'depth': depth, 'frontier': len(frontier), 'ordinary_known': len(ordinary), 'double_known': len(double), 'secs': time.monotonic() - start}), flush=True)
    for t, d in double.items():
        if ordinary.get(t) == d:
            print(json.dumps({'MINIMUM_DOUBLE_COUNTEREXAMPLE': graphs[t], 'minimum': d, 'program': double_witness[t]}), flush=True)
print(json.dumps({'minima': [{'edges': e, 'ordinary': ordinary.get(t), 'double': double.get(t), 'double_program': double_witness.get(t)} for t, e in graphs.items()]}, indent=2), flush=True)
