import itertools
import json
from pathlib import Path

n = 13
offsets = (0, 1, 3, 9)
inc = [[(p - l) % n in offsets for l in range(n)] for p in range(n)]
assert all(sum(inc[p][l] and inc[r][l] for l in range(n)) == 1
           for p in range(n) for r in range(p + 1, n))


def permutation_tables(k):
    result = []
    for perm in itertools.permutations(range(k)):
        table = [sum(1 << perm[i] for i in range(k) if mask >> i & 1) for mask in range(1 << k)]
        result.append((perm, table))
    return result


all_patterns = []
for k in (4, 5, 6):
    tables = permutation_tables(k)
    patterns = {}
    for chosen in itertools.combinations(range(n), k):
        groups = {}
        for l in range(n):
            mask = sum(1 << i for i, p in enumerate(chosen) if inc[p][l])
            if mask:
                groups.setdefault(mask, []).append(l)
        masks = tuple(sorted(groups))
        canonical, perm = min((tuple(sorted(table[m] for m in masks)), perm) for perm, table in tables)
        if canonical in patterns:
            patterns[canonical]['subset_count'] += 1
            continue
        grouped = [{'points': [i for i in range(k) if mask >> i & 1],
                    'original_lines': groups[mask], 'private': mask.bit_count() == 1}
                   for mask in masks]
        g = len(masks)
        e = sum(mask.bit_count() for mask in masks)
        # Brute-force vertex covers on the point side certify the matching/cover count.
        min_cover = min(mask.bit_count() + sum(bool(group & ~mask) for group in masks)
                        for mask in range(1 << k))
        patterns[canonical] = {
            'k': k, 'representative_points': chosen, 'subset_count': 1,
            'canonical_masks': canonical, 'representative_to_canonical_permutation': perm,
            'groups': grouped, 'G': g, 'inputs': k + g, 'E': e,
            'minimum_vertex_cover': min_cover,
            'point_star_size': e + k - 1,
            'minimum_star_size': e + min_cover - 1,
            'one_below_retention_budget': e - g - 1,
            'nontrivial_line_sizes': sorted((mask.bit_count() for mask in masks if mask.bit_count() > 1), reverse=True),
            'private_points': [i for i in range(k) if (1 << i) in groups],
        }
    all_patterns.extend(sorted(patterns.values(), key=lambda p: (p['one_below_retention_budget'], p['inputs'], p['canonical_masks'])))

result = {'plane': 'PG(2,3), cyclic difference set {0,1,3,9} modulo13',
          'subset_total': sum(p['subset_count'] for p in all_patterns),
          'patterns': all_patterns}
Path('/tmp/oec/pequalnp-pilot-76/structural-q3-frontiers.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'subset_total': result['subset_total'], 'pattern_count': len(all_patterns),
    'patterns': [{k: p[k] for k in ('k', 'representative_points', 'subset_count', 'G', 'E', 'inputs',
        'one_below_retention_budget', 'point_star_size', 'minimum_vertex_cover', 'nontrivial_line_sizes', 'private_points')}
        for p in all_patterns]}, indent=2))
