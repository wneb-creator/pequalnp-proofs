import argparse
import itertools
import json
from pathlib import Path

import numpy as np

from tailor_bank_rectangles import Oracle, profile


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('banks')
    ap.add_argument('matrices')
    ap.add_argument('output')
    args = ap.parse_args()
    src = Path(args.banks).read_text()
    banks = json.loads(src) if src.lstrip().startswith('[') else [json.loads(x) for x in src.splitlines()]
    banks = list({tuple(b['state']): b for b in banks}.values())
    files = sorted(Path(args.matrices).glob('Dynamic*.json'))
    matrices = [json.loads(p.read_text()) for p in files]
    oracles = {}
    cache = [{} for _ in matrices]
    results = []
    for bank in banks:
        roots = [int(x, 16) for x in bank['state']]
        profiles = [profile(g) for g in roots]
        costs, margins = [], []
        for mi, matrix in enumerate(matrices):
            w = np.array(matrix['weights'], dtype=np.int64)
            for p in set(profiles):
                if p not in cache[mi]:
                    if p not in oracles:
                        oracles[p] = Oracle(*p)
                    cache[mi][p] = oracles[p].maximum(w)
            root_costs = [cache[mi][p] for p in profiles]
            costs.append(root_costs)
            margins.append(matrix['total'] - sum(root_costs))
        results.append({'node': bank['node'], 'entries': bank['entries'],
                        'remaining': bank['remaining'], 'margins': margins,
                        'root_costs': costs, 'covered': any(x > 0 for x in margins)})
    covered = [{i for i, b in enumerate(results) if b['margins'][mi] > 0}
               for mi in range(len(matrices))]
    target = set().union(*covered)
    best = None
    for n in range(1, len(matrices) + 1):
        good = [c for c in itertools.combinations(range(len(matrices)), n)
                if set().union(*(covered[i] for i in c)) == target]
        if good:
            best = min(good, key=lambda c: sum(max(abs(w) for row in matrices[i]['weights']
                                                 for w in row).bit_length() for i in c))
            break
    summary = {'bank_count': len(banks), 'matrix_count': len(matrices),
               'matrix_names': [m['name'] for m in matrices],
               'covered_count': len(target), 'individual_cover_counts': [len(c) for c in covered],
               'selected': [matrices[i]['name'] for i in best or []],
               'uncovered': [b['node'] for b in results if not b['covered']],
               'unique_profiles': len(oracles)}
    output = Path(args.output)
    assert not output.exists()
    output.mkdir(parents=True)
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    (output / 'banks.json').write_text(json.dumps(banks, indent=2) + '\n')
    (output / 'selected-matrices.json').write_text(json.dumps([matrices[i] for i in best or []], indent=2) + '\n')
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
