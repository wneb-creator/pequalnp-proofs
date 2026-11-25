import argparse
import json
import time
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

from tailor_bank_rectangles import Oracle


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('census')
    args = ap.parse_args()
    root = Path(args.census)
    profiles = json.loads((root / 'profiles.json').read_text())
    weights = json.loads((root / 'weights.json').read_text())
    arrays = [np.array(w['weights'], dtype=np.int64) for w in weights]
    start = time.monotonic()
    groups = defaultdict(list)
    for i, r in enumerate(profiles):
        p, n, w = r['positive_mask'], r['negative_false_mask'], r['weight']
        ps = [j for j in range(weights[w]['rows']) if p >> j & 1]
        ns = [j for j in range(weights[w]['cols']) if n >> j & 1]
        actual = Oracle(ps, ns).maximum(arrays[w])
        assert actual == r['cost'], (i, r, actual)
        if p and n:
            groups[w, r['cost']].append(r)
        if i % 10000 == 0:
            print(json.dumps({'audited': i + 1, 'seconds': time.monotonic() - start}), flush=True)
    audit_seconds = time.monotonic() - start
    kept = []
    for key, rows in groups.items():
        rows.sort(key=lambda r: r['positive_mask'].bit_count() + r['negative_false_mask'].bit_count(), reverse=True)
        local = []
        for r in rows:
            p, n = r['positive_mask'], r['negative_false_mask']
            if not any(p & pp == p and n & nn == n for pp, nn in local):
                local.append((p, n))
                kept.append(r)
    literals = []
    grouped_kept = defaultdict(list)
    for r in kept:
        grouped_kept[r['weight'], r['cost']].append(r)
    for (w, c), rows in grouped_kept.items():
        width = weights[w]['rows'] + weights[w]['cols']
        packed = 0
        for i, r in enumerate(rows):
            code = r['positive_mask'] | (r['negative_false_mask'] << weights[w]['rows'])
            packed |= code << (width * i)
        literals.append(f'({w}, {c}, {len(rows)}, 0x{packed:x})')
    summary = {'original_profiles': len(profiles), 'all_costs_exactly_recomputed': True,
               'audit_seconds': audit_seconds, 'maximal_profiles': len(kept),
               'groups': len(groups), 'literal_bytes': len(('\n'.join(literals) + '\n').encode()),
               'smaller_side_subsets': sum(1 << min(r['positive_mask'].bit_count(), r['negative_false_mask'].bit_count()) for r in kept),
               'by_weight': dict(Counter(r['weight'] for r in kept)),
               'seconds': time.monotonic() - start}
    (root / 'maximal-profiles.json').write_text(json.dumps(kept, indent=2) + '\n')
    (root / 'profile-literals.txt').write_text('\n'.join(literals) + '\n')
    (root / 'compression-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
