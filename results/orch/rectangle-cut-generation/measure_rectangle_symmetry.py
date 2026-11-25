import argparse
import json
import time
from pathlib import Path

import numpy as np

from tailor_bank_rectangles import EDGES, Oracle


def automorphisms():
    adj = {tuple(sorted(e)) for e in EDGES}
    found = []
    def rec(p, unused):
        i = len(p)
        if i == 10:
            found.append(tuple(p))
            return
        for v in unused:
            if all(((min(i, j), max(i, j)) in adj) ==
                   ((min(v, p[j]), max(v, p[j])) in adj) for j in range(i)):
                rec(p + [v], [x for x in unused if x != v])
    rec([], list(range(10)))
    assert len(found) == 120
    return found


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('banks')
    ap.add_argument('matrices')
    ap.add_argument('output')
    args = ap.parse_args()
    banks = json.loads(Path(args.banks).read_text())
    matrices = json.loads(Path(args.matrices).read_text())
    perms = automorphisms()
    rows = [[sum(((r >> i) & 1) << p[i] for i in range(10)) for r in range(1024)]
            for p in perms]
    roots = sorted({int(g, 16) for b in banks for g in b['state']})
    root_index = {g: i for i, g in enumerate(roots)}
    bank_ids = [[root_index[int(g, 16)] for g in b['state']] for b in banks]
    start = time.monotonic()
    costs = np.zeros((len(matrices), 120, len(roots)), dtype=np.int64)
    profile_counts = []
    for mi, m in enumerate(matrices):
        w = np.array(m['weights'], dtype=np.int64)
        cache = {}
        for pi, row in enumerate(rows):
            positive = [row[r] for r in m['positive_rows']]
            negative = [row[r] for r in m['negative_rows']]
            for ri, g in enumerate(roots):
                key = (tuple(i for i, r in enumerate(positive) if (g >> r) & 1),
                       tuple(i for i, r in enumerate(negative) if not ((g >> r) & 1)))
                if key not in cache:
                    cache[key] = Oracle(*key).maximum(w)
                costs[mi, pi, ri] = cache[key]
        profile_counts.append(len(cache))
        print(json.dumps({'matrix': m['name'], 'profiles': len(cache),
                          'seconds': time.monotonic() - start}), flush=True)
    totals = np.array([m['total'] for m in matrices], dtype=np.int64)
    identity = perms.index(tuple(range(10)))
    margins = np.stack([totals[:, None] - costs[:, :, ids].sum(axis=2) for ids in bank_ids])
    results = []
    for b, a in zip(banks, margins):
        flat = int(a.argmax())
        mi, pi = np.unravel_index(flat, a.shape)
        results.append({'node': b['node'], 'raw_best_margin': int(a[:, identity].max()),
                        'symmetry_best_margin': int(a[mi, pi]),
                        'matrix': matrices[mi]['name'], 'permutation': perms[pi],
                        'matrix_covered': [bool(x.max() > 0) for x in a]})
    summary = {'banks': len(banks), 'matrices': len(matrices),
               'raw_covered': sum(r['raw_best_margin'] > 0 for r in results),
               'symmetry_covered': sum(r['symmetry_best_margin'] > 0 for r in results),
               'per_matrix_symmetry_covered': [int((margins[:, i, :].max(axis=1) > 0).sum())
                                               for i in range(len(matrices))],
               'names': [m['name'] for m in matrices],
               'uncovered': [r['node'] for r in results if r['symmetry_best_margin'] <= 0],
               'profile_counts': profile_counts, 'seconds': time.monotonic() - start}
    output = Path(args.output)
    assert not output.exists()
    output.mkdir(parents=True)
    (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    np.save(output / 'margins.npy', margins)
    (output / 'permutations.json').write_text(json.dumps(perms) + '\n')
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
