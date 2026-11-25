import json
from itertools import combinations
from pathlib import Path

data_path = Path('/tmp/oec/pequalnp-pilot-62/collinear3-full-truth.json')
data = json.loads(data_path.read_text())
vertices = data['vertices']
negative = data['maximal_negative_masks']
allowed = [not any(mask & row == mask for row in negative)
           for mask in range(1 << len(vertices))]
minterms = [mask for mask, value in enumerate(allowed) if value and
            all(not allowed[mask ^ (1 << i)]
                for i in range(len(vertices)) if mask >> i & 1)]
edges = set(data['positive_edges'])
assert set(mask for mask in minterms if mask.bit_count() == 2) == edges
triples = [mask for mask in minterms if mask.bit_count() == 3]
assert len(minterms) == len(edges) + len(triples)
point_triples = []
line_triples = []
for mask in triples:
    actual = [vertices[i] for i in range(len(vertices)) if mask >> i & 1]
    if all(v < 13 for v in actual):
        point_triples.append(actual)
    else:
        assert all(v >= 13 for v in actual)
        lines = [v - 13 for v in actual]
        center = [p for p in range(13)
                  if all((p - line) % 13 in [0, 1, 3, 9] for line in lines)]
        assert len(center) == 1
        line_triples.append({'lines': lines, 'center': center[0]})
centers = {}
for triple in line_triples:
    center = str(triple['center'])
    centers[center] = centers.get(center, 0) + 1
print(json.dumps({
    'scope': 'ordinary exhaustive Python computation, not Lean checked',
    'assignments': len(allowed),
    'maximal_negative_rows': len(negative),
    'minimal_positive_edges': len(edges),
    'minimal_point_triples': point_triples,
    'minimal_line_triples': line_triples,
    'line_triples_by_center': centers,
    'higher_degree_minimal_true_supports': 0,
}, indent=2))
