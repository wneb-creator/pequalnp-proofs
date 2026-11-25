import hashlib
import importlib.util
import json
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-178/gap3566/gate_elimination')
spec = importlib.util.spec_from_file_location('review_pendant', BASE / 'pendant_helpers.py')
ph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ph)
rh = ph.rh
manifest = [Path(s) for s in (BASE / 'preservation-amplification.txt').read_text().splitlines() if s]
assert len(manifest) == len(set(manifest)) == 59
assert all(p.parent == BASE and p.is_file() for p in manifest)
hashes = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in manifest}
unchanged = {
    'evolve_amplification.py': 'c3bafed15a4208dc52112b23f2975b56bb8081dcec97172ff4d2e32b065a6c05',
    'evolve_combined.py': 'ec018274a4d75eee72dca86a8260fa255f5a8c33fc6daa65908abe1f1512a93c',
    'pendant_helpers.py': 'db0afe34bc43e2eb1fca196bf64e4ce1f18ded69ba49b23ab90413487297e325',
    'reusable_helpers.py': '093cf1a173360aa38b62957c200e7243a06b2476dcea94bd3f12496dbc9bbe9a',
}
assert all(hashes[name] == sha for name, sha in unchanged.items())
raw = json.loads((BASE / 'saved-amplification-cases.json').read_text())
all_centers = json.loads((BASE / 'all-pendant-centers-results.json').read_text())
assert not all_centers['pending']
saved = {r['source']: r for r in all_centers['cases']}
seen = set()
checked = 0
subsets = 0
max_eligible = 0
by_source = {r['source']: r for r in raw}
for row in raw:
    n, edges, gates, output = row['n'], row['edges'], row['gates'], row['output']
    key = (n, tuple(sorted(tuple(sorted(e)) for e in edges)), tuple(map(tuple, gates)), output)
    if key in seen:
        continue
    seen.add(key)
    actual = ph.audit_case(n, edges, gates, output, max_centers=n)
    expected = saved[row['source']]
    assert not actual.get('witness')
    for field in ('checked_subsets', 'max_cover_rise', 'best_profit', 'deficit', 'eligible'):
        left, right = actual[field], expected[field]
        if field == 'eligible':
            left = json.loads(json.dumps(left))
        assert left == right, (row['source'], field)
    checked += 1
    subsets += actual['checked_subsets']
    max_eligible = max(max_eligible, len(actual['eligible']))
assert checked == 2269 and subsets == 48811 and max_eligible == 8
pendant = {r['source']: r for r in json.loads((BASE / 'pendant-audit-results.json').read_text())['cases']}
materialized = json.loads((BASE / 'materialized-optimal-extensions.json').read_text())
assert len(materialized['cases']) == 288 and not materialized['dirty']
for expected in materialized['cases']:
    row = by_source[expected['source']]
    n, edges, gates, output = row['n'], row['edges'], row['gates'], row['output']
    compact, co, _ = ph.compact_data(n, gates, output)
    ext = ph.extend(n, edges, compact, co, pendant[row['source']]['best_choices'])
    N = ext['n']
    ee = tuple(sorted(tuple(sorted(e)) for e in ext['edges']))
    _, tau, F = rh.graph_data(N, ee)
    compact, co, values = ph.compact_data(N, ext['gates'], ext['output'])
    assert values[co] == F
    profit = len(ee) + tau - 1 - len(compact)
    dirty = [j for j, (op, _, _) in enumerate(compact) if op == 0 and values[N + j] & ~F]
    assert profit == expected['profit'] == 0
    assert not dirty and expected['dirty_and_count'] == 0
    assert len(compact) == expected['gates']
trial = json.loads((BASE / 'evolution-combined-3566181.json').read_text())
assert trial['witness'] is None and trial['counters']['incomplete_audits'] == 0
assert trial['best_amplification']['metrics']['amplification_profit'] == 0
replay = json.loads((BASE / 'replayed-saved-audits.json').read_text())
assert len(replay['cases']) == 2269
assert all(not row['helper'].get('witness') and not row['pendant'].get('witness')
           and not (row['combined'] or {}).get('witness') for row in replay['cases'])
assert all(row['helper']['subset_complete'] and
           (row['combined'] is None or row['combined']['subset_complete']) for row in replay['cases'])
print(json.dumps({'manifest_count': len(manifest), 'unchanged_core_sources': True,
                  'uncapped_replay': {'cases': checked, 'subsets': subsets,
                                      'max_eligible': max_eligible, 'counterexamples': 0},
                  'materializations_replayed': 288, 'all_normalized_profit_zero_and_clean': True,
                  'combined_trial': {k: trial[k] for k in ('seconds', 'valid_graphs', 'counters')},
                  'saved_replay_summary': replay['summary'], 'manifest_sha256': hashes}, indent=2))
