from pathlib import Path
import collections
import hashlib
import itertools
import json
import re

ROOT = Path('/tmp/oec/pequalnp-pilot-87')
trace_path = ROOT / 'library_route/copy-first-allrect-oredge-cuts.jsonl'
data = json.loads((ROOT / 'finite_invariants/rectangle-all-certificates.json').read_text())
signals = {}
headers = []
events = collections.Counter()
for line in trace_path.open():
    row = json.loads(line)
    events[row['event']] += 1
    if row['event'] == 'signal':
        assert row['id'] not in signals
        signals[row['id']] = int(row['hex'], 16)
    elif row['event'] == 'header':
        headers.append(row)
    else:
        assert row['event'] == 'rectangle'
assert len(headers) == 1
assert headers[0]['signed'] == 0 and headers[0]['cap'] == 19
assert headers[0]['first'] == 'oredge'
edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
         (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
target = sum(1 << row for row in range(1024)
             if any((row >> a & 1) and (row >> b & 1) for a, b in edges))
assert int(headers[0]['target'], 16) == target
assert all(0 <= word < 2**1024 for word in signals.values())

word_profiles = {}
profile_costs = {}
hits = collections.Counter()
used = set()
last_node = 0
root_occurrences = 0
for line in trace_path.open():
    row = json.loads(line)
    if row['event'] != 'rectangle':
        continue
    assert row['node'] > last_node
    last_node = row['node']
    ci = row['matrix']
    assert 0 <= ci < 13
    matrix = data[ci]
    state = row['state']
    costs = row['root_costs']
    assert state == sorted(state)
    assert row['remaining'] == len(state) - 1
    assert len(state) == len(costs) and len(state) > 0
    assert all(type(c) is int and c >= 0 for c in costs)
    assert row['cost_sum'] == sum(costs) < row['total'] == matrix['total']
    for signal, cost in zip(state, costs):
        used.add(signal)
        key = (ci, signal)
        if key not in word_profiles:
            word = signals[signal]
            ps = tuple(i for i, r in enumerate(matrix['positive_rows']) if word >> r & 1)
            ns = tuple(i for i, r in enumerate(matrix['negative_rows']) if not (word >> r & 1))
            word_profiles[key] = (ci, ps, ns)
        profile = word_profiles[key]
        if profile in profile_costs:
            assert profile_costs[profile] == cost
        profile_costs[profile] = cost
    hits[ci] += 1
    root_occurrences += len(state)
assert used == set(signals)

subsets_checked = 0
for (ci, rows, cols), expected in profile_costs.items():
    weights = data[ci]['weights']
    if len(rows) <= len(cols):
        small, large = rows, cols
        weight = lambda i, j: weights[i][j]
    else:
        small, large = cols, rows
        weight = lambda i, j: weights[j][i]
    best = 0
    for size in range(1, len(small) + 1):
        for subset in itertools.combinations(small, size):
            value = sum(max(0, sum(weight(i, j) for i in subset)) for j in large)
            best = max(best, value)
            subsets_checked += 1
    assert best == expected, (ci, rows, cols, expected, best)

log = (ROOT / 'library_route/copy-first-allrect-oredge-mono19-180.log').read_text()
counts = [int(x) for x in re.search(r'rectangle_hits=([0-9,]+)', log).group(1).split(',') if x]
assert counts == [hits[i] for i in range(13)]
assert 'limit reached' in log and 'finished found=' not in log
report = {
    'trace_sha256': hashlib.sha256(trace_path.read_bytes()).hexdigest(),
    'trace_bytes': trace_path.stat().st_size,
    'event_counts': dict(events),
    'root_occurrences_checked_with_duplicates': root_occurrences,
    'unique_winning_profiles_recomputed': len(profile_costs),
    'rectangle_subsets_enumerated': subsets_checked,
    'trace_totals_match_complete_run_log': True,
    'all_recorded_rectangle_cuts_valid': True,
    'limitation': 'The bounded search stopped before root exhaustion; this validates terminal cuts only, not a full lower-bound certificate.',
}
(ROOT / 'status_review/audit-allrect-trace.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
