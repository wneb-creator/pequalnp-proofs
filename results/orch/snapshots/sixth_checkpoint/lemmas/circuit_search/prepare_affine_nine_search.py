import collections
import itertools
import json
import pathlib
import random
import time
import sys

HERE = pathlib.Path(__file__).resolve().parent
case_index = int(sys.argv[1]) if len(sys.argv)>1 else 0
stem = 'affine9' if case_index == 0 else f'affine9c{case_index}'
case = json.loads((HERE/'affine-nine-owner-gadgets.json').read_text())[case_index]
n, raw, points, budget = case['inputs'], case['raw_inputs'], 9, 43
assert (n, raw) == (29, 21)
edges = {tuple(e) for e in case['edges']}
neighbors = [{b for a, b in edges if a == p} for p in range(points)]
tests = case['tests'].copy()
for x in (1 << i for i in range(raw)):
    extended = x
    for i, f in enumerate(case['features']):
        if any(x >> j & 1 for j in f['raw_indices']):
            extended |= 1 << (raw+i)
    tests.append([extended, 0])
input_values = [sum(((x >> i) & 1) << j for j, (x, _) in enumerate(tests)) for i in range(n)]
target = sum(y << j for j, (_, y) in enumerate(tests))
rng = random.Random(6509)


def build(group, lines, randomized=False):
    terms = [(tuple(group), set(lines))]
    for p in range(points):
        remain = neighbors[p]-lines if p in group else neighbors[p]
        if remain:
            terms.append(((p,), set(remain)))
    sets = [s.copy() for _, s in terms]
    for s in sets:
        order = sorted(enumerate(case['features']), key=lambda item: -len(item[1]['raw_indices']))
        for i, feature in order:
            part = set(feature['raw_indices'])
            if part <= s:
                s.difference_update(part)
                s.add(raw+i)
    gates = []
    while True:
        counts = collections.Counter(pair for s in sets for pair in itertools.combinations(sorted(s), 2))
        if not counts or max(counts.values()) <= 1:
            break
        top = max(counts.values())
        pairs = [pair for pair, count in counts.items() if count == top]
        pair = rng.choice(pairs) if randomized else pairs[0]
        wire = n+len(gates)
        gates.append([1, *pair])
        for s in sets:
            if set(pair) <= s:
                s.difference_update(pair)
                s.add(wire)
    cache = {}
    def gate(op, a, b):
        if a == b:
            return a
        key = (op, *sorted((a, b)))
        if key not in cache:
            cache[key] = n+len(gates)
            gates.append(list(key))
        return cache[key]
    outputs = []
    for (owners, _), s in zip(terms, sets):
        owner = owners[0]
        for p in owners[1:]:
            owner = gate(1, owner, p)
        line = sorted(s)[0]
        for l in sorted(s)[1:]:
            line = gate(1, line, l)
        outputs.append(gate(0, owner, line))
    output = outputs[0]
    for wire in outputs[1:]:
        output = gate(1, output, wire)
    return gates


pool, seen = [], set()
best, checked = 1000, 0
start = time.monotonic()
for size in range(2, 6):
    for group in itertools.combinations(range(points), size):
        union = sorted(set().union(*(neighbors[p] for p in group)))
        max_columns = 7 if size == 2 else 4 if size == 3 else 3
        for selected in itertools.chain.from_iterable(itertools.combinations(union, k) for k in range(2, max_columns+1)):
            lines = set(selected)
            if any(not (neighbors[p] & lines) for p in group):
                continue
            added = {(p, l) for p in group for l in lines}-edges
            if len(added) > 6:
                continue
            checked += 1
            gates = build(group, lines)
            if len(gates) > budget or sum(op == 0 for op, _, _ in gates) < 9:
                continue
            values = input_values.copy()
            for op, a, b in gates:
                values.append(values[a] | values[b] if op else values[a] & values[b])
            result = values[-1]
            assert result & target == target
            bad = (result & ~target).bit_count()
            if bad < best:
                best = bad
                print('BEST', bad, 'gates', len(gates), 'group', group, 'lines', sorted(lines),
                      'added', sorted(added), 'seconds', time.monotonic()-start, flush=True)
            if result not in seen:
                seen.add(result)
                pool.append(dict(gates=gates, group=group, lines=sorted(lines), added=sorted(added),
                                 false=bad, size=len(gates), ands=sum(op == 0 for op, _, _ in gates)))
full = json.loads((HERE/'full63-best-140.json').read_text())
local = {original: i for i, original in enumerate(case['input_original'])}
ren, support, extracted = {}, {}, []
for i in range(26):
    ren[i] = local.get(i, -1)
    support[i] = (1 << local[i]) if i in local and i >= 13 else None
feature_alias = {sum(1 << j for j in f['raw_indices']): raw+i for i, f in enumerate(case['features'])}
for i, (op, a, b) in enumerate(full):
    left, right = ren[a], ren[b]
    support[26+i] = (support[a] | support[b]) if op == 1 and support[a] is not None and support[b] is not None else None
    if left == right:
        ren[26+i] = left
    elif left == -1 or right == -1:
        ren[26+i] = (right if left == -1 else left) if op else -1
    elif support[26+i] in feature_alias:
        ren[26+i] = feature_alias[support[26+i]]
    else:
        ren[26+i] = n+len(extracted)
        extracted.append([op, left, right])
output = ren[26+len(full)-1]
used = {output}
for i in range(len(extracted)-1, -1, -1):
    if n+i in used:
        used.update(extracted[i][1:])
mapping, compact = {i: i for i in range(n)}, []
for i, (op, a, b) in enumerate(extracted):
    if n+i in used:
        mapping[n+i] = n+len(compact)
        compact.append([op, mapping[a], mapping[b]])
values = input_values.copy()
for op, a, b in compact:
    values.append(values[a] | values[b] if op else values[a] & values[b])
assert values[-1] & target == target
assert len(compact) <= budget
pool.append(dict(gates=compact, source='full63-best-140 restriction', false=(values[-1] & ~target).bit_count(),
                 size=len(compact), ands=sum(op == 0 for op, _, _ in compact)))
pool.sort(key=lambda item: (item['false'], item['size']))
assert pool
(HERE/f'{stem}-feature-seeds.json').write_text(json.dumps(pool))
lines = [str(len(pool))]
for item in pool:
    lines.append(str(len(item['gates'])))
    lines.extend(' '.join(map(str, g)) for g in item['gates'])
(HERE/f'{stem}-feature-seeds.txt').write_text('\n'.join(lines)+'\n')
with (HERE/f'{stem}-feature-tests.txt').open('w') as f:
    f.write(f'{len(tests)}\n')
    for x, y in tests:
        f.write(f'{x} {y}\n')
print('DONE', checked, 'pool', len(pool), 'best', best, 'seconds', time.monotonic()-start, flush=True)
