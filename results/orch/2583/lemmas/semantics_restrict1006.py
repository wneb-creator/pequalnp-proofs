from itertools import product
import json
import time


def minimal(terms):
    kept = []
    for t in sorted(set(terms), key=lambda t: (t.bit_count(), t)):
        if not any(s & t == s for s in kept):
            kept.append(t)
    return kept


gates = []


def gate(op, a, b):
    gates.append((op, a, b))
    return 10 + len(gates)


def ors(xs):
    out = xs[0]
    for x in xs[1:]:
        out = gate('or', out, x)
    return out


g0 = gate('and', ors([7, 10]), ors([6, 9]))
g1 = gate('and', 2, ors([5, 10, g0]))
g2 = gate('and', 0, ors([9, 10]))
g3 = gate('and', ors([8, g0]), ors([4, 5]))
g4 = gate('and', ors([4, 8]), ors([1, g0]))
g5 = gate('and', 3, ors([6, 7]))
output = ors([g1, g2, g3, g4, g5])
polys = [[1 << i] for i in range(11)]
for op, a, b in gates:
    terms = polys[a] + polys[b] if op == 'or' else [u | v for u in polys[a] for v in polys[b]]
    polys.append(minimal(terms))
terms = polys[output]


def graph_data(poly):
    if not poly or any(t.bit_count() != 2 for t in poly):
        return None
    adj = [set() for _ in range(11)]
    for e in poly:
        a, b = [i for i in range(11) if e >> i & 1]
        adj[a].add(b)
        adj[b].add(a)
    color = {}
    for start in range(11):
        if not adj[start] or start in color:
            continue
        color[start] = 0
        todo = [start]
        while todo:
            u = todo.pop()
            for v in adj[u]:
                if v in color:
                    if color[v] == color[u]:
                        return None
                else:
                    color[v] = 1 - color[u]
                    todo.append(v)
    if any(len(adj[a] & adj[b]) > 1 for a in range(11) for b in range(a)):
        return None
    match = {}

    def augment(u, seen):
        for v in adj[u]:
            if v in seen:
                continue
            seen.add(v)
            if v not in match or augment(match[v], seen):
                match[v] = u
                return True
        return False

    for u in color:
        if color[u] == 0:
            augment(u, set())
    return len(poly) + len(match) - 1, len(color), len(match)


def simplify(states, mapping=None):
    if mapping is None:
        mapping = list(range(11))
    wires = [mapping[i] if x == 2 else -1 if x == 1 else -2 for i, x in enumerate(states)]
    new_gates = []
    wire_polys = {-1: (0,), -2: ()}
    wire_polys.update({i: (1 << i,) for i in range(11)})
    semantic_wire = {p: w for w, p in wire_polys.items()}
    for op, a0, b0 in gates:
        a, b = sorted((wires[a0], wires[b0]))
        pa, pb = wire_polys[a], wire_polys[b]
        terms = pa + pb if op == 'or' else [u | v for u in pa for v in pb]
        poly = tuple(minimal(terms))
        if poly in semantic_wire:
            w = semantic_wire[poly]
        else:
            w = 11 + len(new_gates)
            new_gates.append((op, a, b))
            wire_polys[w] = poly
            semantic_wire[poly] = w
        wires.append(w)
    seen = set()

    def visit(w):
        if w < 11 or w in seen:
            return
        seen.add(w)
        _, a, b = new_gates[w - 11]
        visit(a)
        visit(b)

    visit(wires[output])
    return len(seen), wires[output], new_gates


def restriction_search():
    start = time.monotonic()
    stats = {'restrictions': 0, 'quadratic': 0, 'bipartite_squarefree': 0, 'improvements': 0}
    best = None
    for states in product(range(3), repeat=11):
        stats['restrictions'] += 1
        zero = sum(1 << i for i, s in enumerate(states) if s == 0)
        one = sum(1 << i for i, s in enumerate(states) if s == 1)
        poly = minimal(t & ~one for t in terms if not t & zero)
        if not poly or any(t.bit_count() != 2 for t in poly):
            continue
        stats['quadratic'] += 1
        data = graph_data(poly)
        if data is None:
            continue
        stats['bipartite_squarefree'] += 1
        budget, n, cover = data
        size, out, new_gates = simplify(states)
        delta = size - budget
        if best is None or (delta, -len(poly), -n) < (best['delta'], -len(best['edges']), -best['n']):
            best = {'delta': delta, 'states': states, 'edges': poly, 'n': n,
                    'cover': cover, 'budget': budget, 'size': size, 'output': out,
                    'gates': new_gates}
        if delta < 0:
            stats['improvements'] += 1
            print('IMPROVEMENT', json.dumps(best), flush=True)
    print(json.dumps({'stats': stats, 'best': best, 'base_size': len(gates),
                      'base_minterms': terms, 'seconds': time.monotonic() - start}, indent=2))


if __name__ == '__main__':
    restriction_search()
