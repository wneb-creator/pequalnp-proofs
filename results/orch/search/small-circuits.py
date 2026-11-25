import itertools
import json
import time
from pathlib import Path

OUT = Path('/tmp/oec/pequalnp-pilot-66')


def enumerate_graphs(n):
    pairs = list(itertools.combinations(range(n), 2))
    graphs = {}
    for bits in range(1 << len(pairs)):
        edges = [e for k, e in enumerate(pairs) if bits >> k & 1]
        eset = set(edges)
        adjacent = lambda a, b: tuple(sorted((a, b))) in eset
        if any(all(adjacent(p[i], p[(i + 1) % size]) for i in range(size))
               for size in (3, 4) for p in itertools.permutations(range(n), size)):
            continue
        truth = sum(1 << x for x in range(1 << n)
                    if any(x >> a & 1 and x >> b & 1 for a, b in edges))
        graphs[truth] = edges
    return graphs


def ownership(n, gates, edges):
    answer = []
    cones = []
    for j, (op, a, b) in enumerate(gates):
        cs = set()
        for w in (a, b):
            if n <= w < n + j:
                cs.add(w - n)
                cs.update(cones[w - n])
        cones.append(cs)
    for j, (op, a, b) in enumerate(gates):
        if op != 'and':
            continue
        owned = []
        for u, v in edges:
            wires = [i in (u, v) for i in range(n)]
            for operator, x, y in gates:
                wires.append(wires[x] and wires[y] if operator == 'and' else wires[x] or wires[y])
            if wires[n + j] and not any(gates[i][0] == 'and' and wires[n + i] for i in cones[j]):
                owned.append([u, v])
        answer.append({'gate': j, 'owned': owned})
    return answer


def search(n):
    targets = enumerate_graphs(n)
    variables = tuple(sum(1 << x for x in range(1 << n) if x >> i & 1) for i in range(n))
    found = {0: {'edges': [], 'size': 0, 'gates': [], 'ownership': []}}
    states = {(): ()}
    metrics = []
    for depth in range(1, 8):
        next_states = {}
        for extra, gates in states.items():
            values = variables + extra
            value_set = set(values)
            # The saved extra tuple gives evaluation order; key gives semantic set.
            for a, b in itertools.combinations(range(len(values)), 2):
                for op, value in [('and', values[a] & values[b]), ('or', values[a] | values[b])]:
                    if value in value_set:
                        continue
                    new_extra = extra + (value,)
                    key = tuple(sorted(new_extra))
                    if key in next_states:
                        continue
                    new_gates = gates + ((op, a, b),)
                    next_states[key] = (new_extra, new_gates)
                    if value in targets and value not in found:
                        owned = ownership(n, new_gates, targets[value])
                        found[value] = {'edges': targets[value], 'size': depth,
                                        'gates': new_gates, 'ownership': owned}
        metrics.append({'depth': depth, 'states': len(next_states), 'graphs_found': len(found)})
        print(n, metrics[-1], flush=True)
        if len(found) == len(targets):
            break
        states = {extra: gates for extra, gates in next_states.values()}
    assert len(found) == len(targets)
    bad = [r for r in found.values() if any(not a['owned'] for a in r['ownership'])]
    result = {'n': n, 'graph_count': len(targets), 'metrics': metrics,
              'bad_witness_count': len(bad), 'graphs': list(found.values())}
    (OUT / f'small-circuits-n{n}.json').write_text(json.dumps(result, indent=2))
    print('DONE', n, 'graphs', len(targets), 'bad witnesses', len(bad), flush=True)


start = time.time()
for n in range(1, 5):
    search(n)
cycle = [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]
gates = [('or', 1, 4), ('and', 0, 5), ('or', 1, 3), ('and', 2, 7),
         ('and', 3, 4), ('or', 6, 8), ('or', 10, 9)]
print('C5 7-gate construction:', ownership(5, gates, cycle), flush=True)
print('seconds', time.time() - start, flush=True)
