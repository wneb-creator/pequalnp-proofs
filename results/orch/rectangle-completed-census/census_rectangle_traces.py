import argparse
import hashlib
import gzip
import json
import time
from collections import Counter
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('output')
    ap.add_argument('traces', nargs='*')
    args = ap.parse_args()
    base = Path(__file__).resolve().parent
    mapping = json.loads((base / 'trace-map.json').read_text())
    expectations = {str((base / m['archive_relative_path']).resolve()): m['uncompressed_sha256'] for m in mapping}
    if not args.traces:
        args.traces = list(expectations)
    builtins = json.loads((base / 'rectangle-all-certificates.json').read_text())
    approved = {m['id']: m for m in json.loads((base / 'dynamic-loader/matrices-v3.json').read_text())}
    weights, weight_ids, matrices, matrix_ids = [], {}, [], {}

    def register(m):
        p, n = len(m['positive_rows']), len(m['negative_rows'])
        assert len(m['weights']) == p and all(len(row) == n for row in m['weights'])
        assert sum(map(sum, m['weights'])) == m['total']
        wk = (p, n, tuple(w for row in m['weights'] for w in row))
        if wk not in weight_ids:
            weight_ids[wk] = len(weights)
            weights.append({'rows': p, 'cols': n, 'weights': m['weights'], 'total': m['total']})
        wi = weight_ids[wk]
        mk = (wi, tuple(m['positive_rows']), tuple(m['negative_rows']))
        if mk not in matrix_ids:
            matrix_ids[mk] = len(matrices)
            matrices.append({'weight': wi, 'positive_rows': m['positive_rows'],
                             'negative_rows': m['negative_rows'], 'total': m['total']})
        return matrix_ids[mk]

    profiles, profile_signals = {}, Counter()
    results = []
    direct_subset_tests = 0
    start = time.monotonic()
    for filename in args.traces:
        path = Path(filename).resolve()
        local_matrices = [register(m) for m in builtins]
        references, signals, events, hits = {}, {}, Counter(), Counter()
        occurrence_counts = Counter()
        digest = hashlib.sha256()
        uncompressed_bytes = 0
        opener = gzip.open if path.suffix == '.gz' else open
        with opener(path, 'rb') as f:
            for line in f:
                digest.update(line)
                uncompressed_bytes += len(line)
                d = json.loads(line)
                events[d['event']] += 1
                if d['event'] == 'header':
                    assert d['signed'] == 0 and d['cap'] == 19 and d['first'] == 'oredge'
                elif d['event'] == 'matrix_loaded':
                    expected = approved[d['id']]
                    assert all(d[k] == expected[k] for k in ['positive_rows', 'negative_rows', 'weights', 'total'])
                    assert d['matrix'] == len(local_matrices)
                    local_matrices.append(register(d))
                elif d['event'] == 'rectangle':
                    mi = local_matrices[d['matrix']]
                    m = matrices[mi]
                    assert d['total'] == m['total']
                    assert len(d['state']) == len(d['root_costs']) == d['remaining'] + 1
                    assert all(isinstance(c, int) and c >= 0 for c in d['root_costs'])
                    assert sum(d['root_costs']) == d['cost_sum'] < d['total']
                    hits[mi] += 1
                    for signal, cost in zip(d['state'], d['root_costs']):
                        key = (mi, signal)
                        assert key not in references or references[key] == cost
                        references[key] = cost
                        occurrence_counts[key] += 1
                elif d['event'] == 'signal':
                    value = int(d['hex'], 16)
                    assert 0 <= value < 1 << 1024
                    assert d['id'] not in signals or signals[d['id']] == value
                    signals[d['id']] = value
        for (mi, sid), cost in references.items():
            g, m = signals[sid], matrices[mi]
            pm = sum(((g >> r) & 1) << i for i, r in enumerate(m['positive_rows']))
            nm = sum((1 - ((g >> r) & 1)) << i for i, r in enumerate(m['negative_rows']))
            key = (m['weight'], pm, nm)
            assert key not in profiles or profiles[key] == cost
            profiles[key] = cost
            profile_signals[key] += 1
            if pm and nm:
                direct_subset_tests += occurrence_counts[mi, sid] * (1 << min(pm.bit_count(), nm.bit_count()))
        if str(path) in expectations:
            assert digest.hexdigest() == expectations[str(path)]
        result = {'trace': str(path), 'bytes': uncompressed_bytes, 'archive_bytes': path.stat().st_size, 'sha256': digest.hexdigest(),
                  'events': dict(events), 'matrix_signal_obligations': len(references),
                  'root_cost_occurrences': sum(occurrence_counts.values()),
                  'signals': len(signals), 'loaded_matrices': len(local_matrices),
                  'cut_matrix_hits': dict(hits)}
        results.append(result)
        print(json.dumps({k: v for k, v in result.items() if k not in ['cut_matrix_hits']}), flush=True)
    records = [{'weight': wi, 'positive_mask': p, 'negative_false_mask': n,
                'cost': cost, 'source_obligations': profile_signals[(wi, p, n)]}
               for (wi, p, n), cost in sorted(profiles.items())]
    nontrivial = [r for r in records if r['positive_mask'] and r['negative_false_mask']]
    summary = {'traces': len(results), 'trace_bytes': sum(r['bytes'] for r in results),
               'rectangle_events': sum(r['events'].get('rectangle', 0) for r in results),
               'root_cost_occurrences': sum(r['root_cost_occurrences'] for r in results),
               'direct_subset_tests_without_sharing': direct_subset_tests,
               'matrix_instances': len(matrices), 'weight_arrays': len(weights),
               'cost_profiles': len(records), 'nontrivial_profiles': len(nontrivial),
               'smaller_side_subsets': sum(1 << min(r['positive_mask'].bit_count(), r['negative_false_mask'].bit_count()) for r in nontrivial),
               'maximum_smaller_side': max(min(r['positive_mask'].bit_count(), r['negative_false_mask'].bit_count()) for r in nontrivial),
               'seconds': time.monotonic() - start,
               'scope': 'Rectangle-data consistency and census only; full search correctness and Lean replay remain separate.'}
    output = Path(args.output)
    assert not output.exists()
    output.mkdir(parents=True)
    for name, value in [('summary', summary), ('traces', results), ('profiles', records), ('weights', weights), ('matrices', matrices)]:
        (output / f'{name}.json').write_text(json.dumps(value, indent=2) + '\n')
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
