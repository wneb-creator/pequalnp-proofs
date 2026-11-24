import itertools
import json
from pathlib import Path

N = 13
lines = [frozenset((l + d) % N for d in (0, 1, 3, 9)) for l in range(N)]
join = {(a, b): next(l for l in range(N) if a in lines[l] and b in lines[l])
        for a in range(N) for b in range(N) if a != b}
meet = {(a, b): next(iter(lines[a] & lines[b]))
        for a in range(N) for b in range(N) if a != b}

def frame(points):
    return len(set(points)) == 4 and all(
        c not in lines[join[a, b]] for a, b, c in itertools.combinations(points, 3))

def extend(src, dst):
    pmap = dict(zip(src, dst))
    lmap = {}
    while True:
        old = (len(pmap), len(lmap))
        for table, other, operation in ((pmap, lmap, join), (lmap, pmap, meet)):
            for a, b in itertools.combinations(list(table), 2):
                c = operation[a, b]
                d = operation[table[a], table[b]]
                if c in other and other[c] != d:
                    return None
                if c not in other and d in other.values():
                    return None
                other[c] = d
        if old == (len(pmap), len(lmap)):
            break
    if len(pmap) != N or len(lmap) != N:
        return None
    assert all((p in lines[l]) == (pmap[p] in lines[lmap[l]])
               for p in range(N) for l in range(N))
    return {'points': [pmap[i] for i in range(N)], 'lines': [lmap[i] for i in range(N)]}

source = next((1, 0, a, b) for a in range(N) for b in range(N) if frame((1, 0, a, b)))
answer = None
for a, b in itertools.product(range(N), repeat=2):
    target = (0, 1, a, b)
    if frame(target):
        answer = extend(source, target)
        if answer is not None and answer['lines'][0] == 0:
            break
assert answer is not None
assert answer['points'][1] == 0 and answer['lines'][0] == 0
answer['source_frame'] = source
answer['target_frame'] = target
answer['checked_incidence_pairs'] = N * N
answer['explanation'] = 'Maps incident flag (1,0) to (0,0). Together with translations and multiplier3, this gives transitivity on all52 flags.'
Path('/tmp/oec/pequalnp-pilot-20/plane-automorphism.json').write_text(json.dumps(answer, indent=2) + '\n')
print(json.dumps(answer))
