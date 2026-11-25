from itertools import combinations
from pathlib import Path
import json

TYPES = list(range(1, 15))
ADJ = {a: {b for b in TYPES if a != b and a | b == 15} for a in TYPES}
FORBIDDEN = []
for count in (3, 4):
    for xs in combinations(TYPES, count):
        union = 0
        for x in xs:
            union |= x
        if union == 15 and all(a | b != 15 for a, b in combinations(xs, 2)):
            FORBIDDEN.append(sum(1 << (x-1) for x in xs))


def classify(mask):
    if any(mask & bad == bad for bad in FORBIDDEN):
        return None
    vertices = {x for x in TYPES if mask >> (x-1) & 1}
    adjacency = {x: ADJ[x] & vertices for x in vertices}
    if not vertices or any(not a for a in adjacency.values()):
        return None
    if any(len(adjacency[a] & adjacency[b]) > 1 for a, b in combinations(vertices, 2)):
        return None
    color, components = {}, 0
    for start in vertices:
        if start in color:
            continue
        components += 1
        color[start] = 0
        stack = [start]
        while stack:
            a = stack.pop()
            for b in adjacency[a]:
                if b in color:
                    if color[b] == color[a]:
                        return None
                else:
                    color[b] = 1-color[a]
                    stack.append(b)
    edges = [(a, b) for a in vertices for b in adjacency[a] if a < b]
    assert len(edges) == len(vertices)-components, (mask, edges)
    return {'mask': mask, 'types': sorted(vertices), 'edges': edges,
            'components': components,
            'degree_sequence': sorted((len(a) for a in adjacency.values()), reverse=True)}


if __name__ == '__main__':
    results = [result for mask in range(1 << 14) if (result := classify(mask))]
    shapes = {}
    for r in results:
        key = str((r['components'], r['degree_sequence']))
        shapes[key] = shapes.get(key, 0)+1
    data = {'presence_profiles_checked': 1 << 14, 'forbidden_independent_covers': len(FORBIDDEN),
            'surviving': len(results), 'all_forests': True, 'shapes': shapes, 'cases': results}
    root = Path('/tmp/oec/pequalnp-pilot-110/counterexample2583')
    (root/'four-clause-blocks.json').write_text(json.dumps(data, indent=2))
    print(json.dumps({k: v for k, v in data.items() if k != 'cases'}))
