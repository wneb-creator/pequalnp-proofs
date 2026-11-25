import collections
import itertools
import json
import pathlib
import random
import time

HERE = pathlib.Path(__file__).resolve().parent
case = json.loads((HERE / 'k9_arc_4_8_10_12.json').read_text())
edges = {tuple(e) for e in case['edges']}
neighbors = [{l for p, l in edges if p == i} for i in range(9)]
tests = case['tests']
signatures = [sum(((x >> i) & 1) << j for j, (x, _) in enumerate(tests)) for i in range(22)]
target = sum(y << j for j, (_, y) in enumerate(tests))
rng = random.Random(65017)


def build(group, lines, randomize=False):
    gates = []
    terms = [(tuple(group), set(lines))]
    for p in range(9):
        remainder = neighbors[p] - lines if p in group else neighbors[p]
        if remainder:
            terms.append(((p,), set(remainder)))
    # Common pair elimination over all pure-line OR expressions.
    sets = [s.copy() for _, s in terms]
    while True:
        counts = collections.Counter(pair for s in sets for pair in itertools.combinations(sorted(s), 2))
        if not counts or max(counts.values()) <= 1:
            break
        best = max(counts.values())
        pairs = [p for p, n in counts.items() if n == best]
        pair = rng.choice(pairs) if randomize else pairs[0]
        wire = 22 + len(gates)
        gates.append([1, *pair])
        for s in sets:
            if set(pair) <= s:
                s.difference_update(pair)
                s.add(wire)
    outputs = []
    cache = {}
    def gate(op, a, b):
        if a == b:
            return a
        key = (op, *sorted((a, b)))
        if key not in cache:
            cache[key] = 22 + len(gates)
            gates.append(list(key))
        return cache[key]
    for (owners, _), s in zip(terms, sets):
        own = owners[0]
        for p in owners[1:]:
            own = gate(1, own, p)
        line = sorted(s)[0]
        for l in sorted(s)[1:]:
            line = gate(1, line, l)
        outputs.append(gate(0, own, line))
    output = outputs[0]
    for wire in outputs[1:]:
        output = gate(1, output, wire)
    return gates


best = 1000
pool = []
seen = set()
start = time.monotonic()
checked = 0
for size in range(2, 6):
    for group in itertools.combinations(range(9), size):
        union = sorted(set().union(*(neighbors[p] for p in group)))
        max_columns = 5 if size == 2 else 3 if size == 3 else 2
        for selected in itertools.chain.from_iterable(itertools.combinations(union, k) for k in range(2, max_columns + 1)):
            lines = set(selected)
            if len(lines) < 2 or any(not (neighbors[p] & lines) for p in group):
                continue
            added = {(p, l) for p in group for l in lines} - edges
            if len(added) > 4:
                continue
            checked += 1
            gates = build(group, lines)
            if len(gates) > 43:
                continue
            values = signatures.copy()
            for op, a, b in gates:
                values.append(values[a] | values[b] if op else values[a] & values[b])
            result = values[-1]
            assert result & target == target
            bad = (result & ~target).bit_count()
            if bad < best:
                best = bad
                print('BEST', best, 'gates', len(gates), 'group', group, 'lines', sorted(lines),
                      'added', sorted(added), 'seconds', time.monotonic()-start, flush=True)
                (HERE/'k9-rectangle-best.json').write_text(json.dumps(gates))
            if bad <= 67 and result not in seen:
                seen.add(result)
                pool.append(dict(gates=gates, group=group, lines=sorted(lines),
                                 added=sorted(added), false=bad))
print('DONE', checked, 'best', best, 'pool', len(pool), 'seconds', time.monotonic()-start, flush=True)
(HERE/'k9-rectangle-pool.json').write_text(json.dumps(pool))
