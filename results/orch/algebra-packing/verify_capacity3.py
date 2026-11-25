from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

base = Path('/tmp/oec/pequalnp-pilot-62')
data = [int(x) for x in (base / 'singleton-packing-input.txt').read_text().split()]
nr, ne = data[:2]
assert (nr, ne) == (468, 52)
rows = data[2:2 + nr]
edges = data[2 + nr:]
assert len(edges) == 52 and len(set(rows)) == 468
assert all(x.bit_count() == 7 for x in rows)
assert all(x.bit_count() == 2 for x in edges)

blocks = [3, 36, 80, 384]
union = 0
for b in blocks:
    assert b.bit_count() in (1, 2) and not union & b
    union |= b
activity = Counter(sum(bool(r & b) for b in blocks) for r in rows)
assert max(activity) <= 3
removed = sum(bool(e & union) for e in edges)
assert removed - len(blocks) == 28

# Independent, narrower exact enumeration of every four-pair, single-color
# family. This does not independently certify the global upper bound.
single_color = []
for shift in (0, 13):
    caps = sorted({(r >> shift) & 8191 for r in rows
                   if ((r >> shift) & 8191).bit_count() == 4})
    assert len(caps) == 234
    pairs = [(1 << a) | (1 << b) for a, b in combinations(range(13), 2)]
    active = [sum(1 << i for i, c in enumerate(caps) if p & c) for p in pairs]
    total = valid = 0
    supports = Counter()
    def visit(start, chosen, used, intersection):
        global total, valid
        if len(chosen) == 4:
            total += 1
            if intersection == 0:
                valid += 1
                supports[used] += 1
            return
        for i in range(start, len(pairs)):
            if pairs[i] & used:
                continue
            visit(i + 1, chosen + (i,), used | pairs[i], intersection & active[i])
    visit(0, (), 0, (1 << len(caps)) - 1)
    assert total == 135135 and valid == 1053
    single_color.append({
        'side': 'points' if shift == 0 else 'lines',
        'all_four_pair_families': total,
        'valid_four_pair_families': valid,
        'distinct_eight_coordinate_supports': len(supports),
        'valid_partition_multiplicity_histogram': dict(Counter(supports.values())),
    })

depths = [1, 351, 52975, 4532450, 28911402, 20269808, 2608320, 49140, 468]
assert sum(depths) == 56424915
result = {
    'scope': 'Independent witness and same-color-maximizer checks; global upper bound is from C++ exhaustive DFS.',
    'witness_blocks': blocks,
    'witness_vertices': [i for i in range(26) if union >> i & 1],
    'witness_removed_flags': removed,
    'witness_objective': removed - len(blocks),
    'witness_row_activity_histogram': dict(sorted(activity.items())),
    'same_color_independent_enumeration': single_color,
    'full_dfs_feasible_family_count': sum(depths),
    'full_dfs_depth_counts': depths,
    'source_sha256': sha256((base / 'singleton_packing_capacity3.cpp').read_bytes()).hexdigest(),
    'input_sha256': sha256((base / 'singleton-packing-input.txt').read_bytes()).hexdigest(),
}
print(json.dumps(result, indent=2))
(base / 'packing-capacity3-verification.json').write_text(json.dumps(result, indent=2) + '\n')
