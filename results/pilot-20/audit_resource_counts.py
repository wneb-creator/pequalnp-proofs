import hashlib
import json
from pathlib import Path

root = Path('/tmp/oec/pequalnp-pilot-20')
paths = [root / 'search/shannon65-full.json',
         root / 'algebraic/shared-cover/local-types/calibration-core6-global65.json',
         root / 'algebraic/shared-cover/local-types/cnf-core9-global68.json']
neighbors = [sum(1 << ((p - d) % 13) for d in (0, 1, 3, 9)) for p in range(13)]
false_masks = set()
for points in range(1 << 13):
    excluded = 0
    for p in range(13):
        if points >> p & 1:
            excluded |= neighbors[p]
    false_masks.add(points | (((1 << 13) - 1) ^ excluded) << 13)
false_masks = sorted(false_masks)
results = []
for path in paths:
    data = json.loads(path.read_text())
    supports = [1 << i for i in range(26)]
    negatives = [sum(((x >> i) & 1) << j for j, x in enumerate(false_masks)) for i in range(26)]
    counts = {'and': 0, 'wide_or': 0, 'narrow_or': 0}
    unsafe_ands = []
    for j, (a, b, op) in enumerate(data['gates']):
        assert a != b and 0 <= a < 26 + j and 0 <= b < 26 + j and op in (0, 1)
        if op == 0:
            supports.append(supports[a] & supports[b])
            negatives.append(negatives[a] & negatives[b])
            counts['and'] += 1
            if negatives[-1]:
                unsafe_ands.append(j)
        else:
            supports.append(supports[a] | supports[b])
            negatives.append(negatives[a] | negatives[b])
            counts['wide_or' if supports[-1].bit_count() > 1 else 'narrow_or'] += 1
    results.append({'file': path.name, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                    'gates': len(data['gates']), 'counts': counts,
                    'false_closure_tests': len(false_masks),
                    'unsafe_and_indices': unsafe_ands,
                    'output_false_on_closures': negatives[data['output']] == 0})
print(json.dumps(results, indent=2))
