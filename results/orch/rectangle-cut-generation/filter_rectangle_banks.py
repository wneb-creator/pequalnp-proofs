import argparse
import json
from pathlib import Path

import numpy as np

from tailor_bank_rectangles import Oracle


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('banks')
    ap.add_argument('output')
    ap.add_argument('matrices', nargs='+')
    args = ap.parse_args()
    src = Path(args.banks).read_text()
    banks = json.loads(src) if src.lstrip().startswith('[') else [json.loads(x) for x in src.splitlines()]
    banks = list({tuple(b['state']): b for b in banks}.values())
    matrices = [m for path in args.matrices for m in json.loads(Path(path).read_text())]
    cache = [{} for _ in matrices]
    out, results = [], []
    for bank in banks:
        roots = [int(x, 16) for x in bank['state']]
        covering = None
        for i, m in enumerate(matrices):
            w = np.array(m['weights'], dtype=np.int64)
            costs = []
            for g in roots:
                key = (tuple(j for j, r in enumerate(m['positive_rows']) if (g >> r) & 1),
                       tuple(j for j, r in enumerate(m['negative_rows']) if not ((g >> r) & 1)))
                if key not in cache[i]:
                    cache[i][key] = Oracle(*key).maximum(w)
                costs.append(cache[i][key])
            if sum(costs) < m['total']:
                covering = {'node': bank['node'], 'matrix': m['name'],
                            'root_costs': costs, 'margin': m['total'] - sum(costs)}
                break
        if covering:
            results.append(covering)
        else:
            out.append(bank)
    output = Path(args.output)
    assert not output.exists()
    output.mkdir(parents=True)
    (output / 'all-banks.json').write_text(json.dumps(banks, indent=2) + '\n')
    (output / 'uncovered-banks.json').write_text(json.dumps(out, indent=2) + '\n')
    (output / 'covered-results.json').write_text(json.dumps(results, indent=2) + '\n')
    summary = {'banks': len(banks), 'matrices': len(matrices), 'covered': len(results),
               'uncovered': len(out), 'uncovered_nodes': [b['node'] for b in out]}
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
