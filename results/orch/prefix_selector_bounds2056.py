import collections
import hashlib
import itertools
import json
from pathlib import Path

base = Path('/tmp/oec/pequalnp-pilot-121/window2056-sat')

def analyze(data, prefix):
    n = data['n']
    edges = data['edges']
    rows = data['rows']
    assert len(rows) == len(set(rows))
    def target(row):
        return any((row >> a & 1) and (row >> b & 1) for a, b in edges)
    negatives = [row for row in rows if not target(row)]
    assert all(all(target(row | (1 << i)) for i in range(n) if not (row >> i & 1)) for row in negatives)
    indices = [j for j, (op, _, _) in enumerate(prefix) if not op]
    observations = []
    for row in negatives:
        values = [bool(row >> i & 1) for i in range(n)]
        pairs = []
        for j, (op, a, b) in enumerate(prefix):
            assert op in (0, 1) and 0 <= a < n + j and 0 <= b < n + j
            if not op:
                pairs.append((values[a], values[b]))
            values.append(values[a] or values[b] if op else values[a] and values[b])
        observations.append(pairs)
    k = len(indices)
    buckets = []
    for orientations in itertools.product((0, 1), repeat=k):
        counts = collections.Counter(tuple(pairs[i][side] for i, side in enumerate(orientations)) for pairs in observations)
        maximum = max(counts.values())
        buckets.append({'orientations': list(orientations), 'max_bucket': maximum,
                        'and_lower_bound': k + (maximum - 1).bit_length()})
    best = max(buckets, key=lambda x: (x['and_lower_bound'], x['max_bucket']))
    return {'negative_rows': len(negatives), 'fixed_gates': len(prefix), 'fixed_ands': k,
            'and_indices': indices, 'left_only': buckets[0], 'best_orientation': best,
            'orientation_bucket_min': min(x['max_bucket'] for x in buckets),
            'orientation_bucket_max': max(x['max_bucket'] for x in buckets),
            'orientation_bound_min': min(x['and_lower_bound'] for x in buckets),
            'orientation_bound_max': max(x['and_lower_bound'] for x in buckets)}

menu_path = base / 'reused28-prefix-star-menus-2056.json'
plane_path = base / 'plane63-prefix34-2056.data.json'
menu = json.loads(menu_path.read_text())
variants = [analyze(menu, prefix) for prefix in menu['variants']]
plane = json.loads(plane_path.read_text())
fixed = plane['ordered_gates'][:plane['prefix_size']]
assert fixed == plane['positive_gates64'][:plane['prefix_size']]
backup = analyze(plane, fixed)
summary = {'variants': len(variants), 'fixed_ands': sorted(set(v['fixed_ands'] for v in variants)),
           'left_bucket_min': min(v['left_only']['max_bucket'] for v in variants),
           'left_bucket_max': max(v['left_only']['max_bucket'] for v in variants),
           'left_bound_min': min(v['left_only']['and_lower_bound'] for v in variants),
           'left_bound_max': max(v['left_only']['and_lower_bound'] for v in variants),
           'best_bucket_min': min(v['best_orientation']['max_bucket'] for v in variants),
           'best_bucket_max': max(v['best_orientation']['max_bucket'] for v in variants),
           'best_bound_min': min(v['best_orientation']['and_lower_bound'] for v in variants),
           'best_bound_max': max(v['best_orientation']['and_lower_bound'] for v in variants)}
result = {'scope': 'Diagnostic mathematical selector-bucket bound only; no Lean certificate or solver constraint.',
          'input_hashes': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in [menu_path, plane_path]},
          'menu_summary': summary, 'menu_variants': variants, 'full_plane_prefix34': backup}
Path('results/orch/prefix-selector-bounds2056.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'menu_summary': summary, 'full_plane_prefix34': backup}))
