import argparse
import json
import time
from pathlib import Path

import numpy as np

from tailor_bank_rectangles import Oracle, profile, solve


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('banks')
    ap.add_argument('seeds')
    ap.add_argument('output')
    ap.add_argument('--prefix', default='DynamicV2Node')
    ap.add_argument('--minimum-gap', type=float, default=1.)
    ap.add_argument('--seconds', type=float, default=20.)
    ap.add_argument('--iterations', type=int, default=250)
    args = ap.parse_args()
    src = Path(args.banks).read_text()
    banks = json.loads(src) if src.lstrip().startswith('[') else [json.loads(x) for x in src.splitlines()]
    banks = sorted({tuple(b['state']): b for b in banks}.values(),
                   key=lambda b: (-b['entries'], b['node']))
    certificates = json.loads(Path(args.seeds).read_text())
    output = Path(args.output)
    assert not output.exists()
    output.mkdir(parents=True)
    (output / 'banks.json').write_text(json.dumps(banks, indent=2) + '\n')
    (output / 'seed-matrices.json').write_text(json.dumps(certificates, indent=2) + '\n')
    oracles, cache = {}, [{} for _ in certificates]
    results = []
    start = time.monotonic()
    for bank in banks:
        profiles = [profile(int(g, 16)) for g in bank['state']]
        for p in set(profiles):
            if p not in oracles:
                oracles[p] = Oracle(*p)
        covering = None
        for i, cert in enumerate(certificates):
            w = np.array(cert['weights'], dtype=np.int64)
            for p in set(profiles):
                if p not in cache[i]:
                    cache[i][p] = oracles[p].maximum(w)
            margin = cert['total'] - sum(cache[i][p] for p in profiles)
            if margin > 0:
                covering = {'node': bank['node'], 'status': 'covered',
                            'certificate': cert['name'], 'margin': margin}
                break
        if covering:
            results.append(covering)
            print(json.dumps(covering), flush=True)
            continue
        result = solve(bank, args.seconds, args.iterations, output,
                       args.prefix, args.minimum_gap)
        results.append(result)
        if result['status'] == 'exact_separation':
            cert = json.loads(Path(result['file']).read_text())
            certificates.append(cert)
            cache.append({})
        (output / 'progress.json').write_text(json.dumps({'results': results, 'seconds': time.monotonic() - start}, indent=2) + '\n')
    summary = {'results': results, 'seconds': time.monotonic() - start,
               'banks': len(banks), 'certificates': len(certificates),
               'excluded': sum(x['status'] in ['covered', 'exact_separation'] for x in results)}
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    (output / 'all-matrices.json').write_text(json.dumps(certificates, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'results'}), flush=True)


if __name__ == '__main__':
    main()
