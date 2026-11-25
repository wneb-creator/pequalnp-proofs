import hashlib
import importlib.util
import json
from collections import Counter
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-178/gap3566')
GE = BASE / 'gate_elimination'
CS = BASE / 'certificate_search'


def verify_circuit(d):
    n = d.get('n', d.get('inputs'))
    gates = d['gates']
    output = d.get('output', n + len(gates) - 1)
    edges = {tuple(sorted(e)) for e in d['edges']}
    adj = [set() for _ in range(n)]
    for u, v in edges:
        assert 0 <= u < v < n
        adj[u].add(v)
        adj[v].add(u)
    colors = {}
    for seed in range(n):
        if seed in colors:
            continue
        colors[seed] = 0
        queue = [seed]
        for u in queue:
            for v in adj[u]:
                if v not in colors:
                    colors[v] = 1 - colors[u]
                    queue.append(v)
                assert colors[v] != colors[u]
    assert all(len(adj[u] & adj[v]) <= 1 for u in range(n) for v in range(u))
    tau = min(s.bit_count() for s in range(1 << n)
              if all((s >> u) & 1 or (s >> v) & 1 for u, v in edges))
    for assignment in range(1 << n):
        values = [bool((assignment >> i) & 1) for i in range(n)]
        for i, (op, a, b) in enumerate(gates):
            assert 0 <= a < n + i and 0 <= b < n + i
            assert op in (0, 1, 'and', 'or')
            values.append((values[a] and values[b]) if op in (0, 'and')
                          else (values[a] or values[b]))
        expected = any(values[u] and values[v] for u, v in edges)
        assert values[output] == expected
    return {'inputs': n, 'edges': len(edges), 'cover': tau,
            'gates': len(gates), 'profit': len(edges) + tau - 1 - len(gates),
            'assignments': 1 << n}


def main():
    report = {}
    for name in ('pendant-positive-control.json', 'pendant-generalized-control.json'):
        report[name] = verify_circuit(json.loads((GE / name).read_text())['witness'])
    result = json.loads((GE / 'evolution-amplification-3566180.json').read_text())
    assert result['witness'] is None
    assert result['counters']['incomplete_audits'] == 0
    report['amplification_trial'] = {k: result[k] for k in ('seconds', 'valid_graphs', 'counters')}
    report['amplification_best'] = verify_circuit(result['best_amplification'])
    spec = importlib.util.spec_from_file_location('review_combined', GE / 'evolve_combined.py')
    combined = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(combined)
    saved = json.loads((GE / 'evolution-combined-validation.json').read_text())['checks']
    checks = []
    for i, gates in enumerate(combined.load_seeds()):
        _, metrics, _ = combined.evaluate(gates, min_edges=8)
        for field in ('base_gain', 'helper_profit', 'pendant_rise', 'amplification_profit'):
            assert metrics[field] == saved[i][field]
        edges = combined.ea.graph_info(metrics['graph_key'])[4]
        direct = combined.rh.audit_case(14, edges, gates, 14 + len(gates) - 1)
        pendant = combined.ph.audit_case(14, edges, gates, 14 + len(gates) - 1)
        assert direct['subset_complete']
        assert direct['best_extension_profit'] == metrics['helper_profit']
        assert pendant['max_cover_rise'] == metrics['pendant_rise']
        if metrics['pendant_rise']:
            ext = combined.apply_pendant(gates, metrics['graph_key'], metrics['pendant_choices'])
            exact = combined.rh.audit_case(ext['n'], ext['edges'], ext['gates'], ext['output'])
            assert exact['best_extension_profit'] >= metrics['amplification_profit']
        checks.append((metrics['base_gain'], metrics['pendant_rise'], metrics['amplification_profit']))
    assert len(checks) == len(saved) == 22
    report['combined_seed_recheck'] = {'count': len(checks), 'triples': dict(Counter(map(str, checks)))}
    for name in ('pendant-audit-results.json', 'combined-extension-audit-results.json'):
        data = json.loads((GE / name).read_text())
        assert data['summary']['cases'] == len(data['cases'])
        assert not any(row.get('error') or row.get('witness') for row in data['cases'])
        report[name] = data['summary']
    summary = json.loads((CS / 'c8-large-helper-summary.json').read_text())
    assert summary['skip'] == 0 and summary['next_index'] == summary['total_cases'] == 137233
    assert sum(summary['completed_by_cost']) == 137233 and summary['found'] is False
    assert (CS / 'c8-large-helper-sweep.log').read_text().splitlines()[-1] == 'FINISHED done=137233 total=137233 seconds=419.036 found=0'
    report['large_helper_sweep'] = summary
    report['source_hashes'] = {name: hashlib.sha256((GE / name).read_bytes()).hexdigest()
                               for name in ('evolve_amplification.py', 'evolve_combined.py',
                                            'pendant_helpers.py', 'reusable_helpers.py',
                                            'audit_combined_extensions.py')}
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
