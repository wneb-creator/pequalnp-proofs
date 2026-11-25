from pathlib import Path
from collections import Counter
import hashlib
import json
import re

p = Path(__file__).resolve().parent
full = (1 << 1024) - 1
inputs = [sum(1 << r for r in range(1024) if (r >> i) & 1) for i in range(10)]
edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
         (5,7),(7,9),(9,6),(6,8),(8,5)]
target = 0
for a, b in edges:
    target |= inputs[a] & inputs[b]
meta = json.loads((p / 'run-metadata.json').read_text())
assert meta['memo_input'] is None and meta['mono_nine_bound'] == 15
assert '--memo-in' not in meta['command'] and '--mono-nine15' in meta['command']
assert hashlib.sha256((p / 'rectangles-v2.txt').read_bytes()).hexdigest() == meta['matrix_sha256']
source = (p / 'copy_search_weak15.cpp').read_text()
profiles = re.search(r'static const CP profiles\[CP_COUNT\]\s*=\s*\{(.*?)\};', source, re.S)
assert profiles
values = [tuple(map(int, v)) for v in re.findall(r'\{(\d+),(\d+),(\d+),(\d+)\}', profiles.group(1))]
assert len(values) == 1145
assert all((15 if i < 10 else mono) == signed for i, (_, _, mono, signed) in enumerate(values))

events = Counter()
matrix_hits = Counter()
matrices = {}
referenced = set()
signals = {}
with (p / 'rectangles.jsonl').open() as stream:
    for line in stream:
        x = json.loads(line)
        kind = x['event']
        events[kind] += 1
        if kind == 'header':
            assert not x['signed'] and x['cap'] == 19 and x['first'] == 'oredge'
            assert int(x['target'], 16) == target
        elif kind == 'matrix_loaded':
            assert x['matrix'] not in matrices
            assert len(x['weights']) == len(x['positive_rows'])
            assert all(len(row) == len(x['negative_rows']) for row in x['weights'])
            assert sum(map(sum, x['weights'])) == x['total']
            assert all((target >> r) & 1 for r in x['positive_rows'])
            assert all(not ((target >> r) & 1) for r in x['negative_rows'])
            matrices[x['matrix']] = x
        elif kind == 'rectangle':
            matrix_hits[x['matrix']] += 1
            assert x['remaining'] + 1 == len(x['state']) == len(x['root_costs'])
            assert all(c >= 0 for c in x['root_costs'])
            assert sum(x['root_costs']) == x['cost_sum'] < x['total']
            if x['matrix'] >= 13:
                assert x['total'] == matrices[x['matrix']]['total']
            referenced.update(x['state'])
        elif kind == 'signal':
            assert x['id'] not in signals
            signals[x['id']] = int(x['hex'], 16)
        else:
            raise AssertionError(kind)
assert events['header'] == 1 and events['matrix_loaded'] == 13
assert referenced <= signals.keys()

banks = 0
with (p / 'banks.jsonl').open() as stream:
    for line in stream:
        x = json.loads(line)
        assert x['remaining'] + 1 == len(x['state']) and x['entries'] >= 0
        available = set(inputs)
        for d, a, b in x['history']:
            a, b = int(a, 16), int(b, 16)
            assert d in [0, 1] and a in available and b in available
            available.add((a & b) if d == 0 else (a | b))
        assert all(int(v, 16) in available for v in x['state'])
        banks += 1

memo_states = 0
remaining = Counter()
seen = set()
root_present = False
initial = sorted(inputs + [inputs[0] | inputs[1]])
with (p / 'completed-weak15.memo').open() as stream:
    assert stream.readline().split() == ['PNP_COPY_MEMO_V1', '0', '19', 'oredge', '1']
    for line in stream:
        tokens = line.split()
        assert tokens[0] == 'S'
        k, n = map(int, tokens[1:3])
        assert 0 <= k <= 19 and 1 <= n <= k + 1 and len(tokens[3:]) == n
        assert all(re.fullmatch(r'0x[0-9a-f]{256}', value) for value in tokens[3:])
        words = [int(value, 16) for value in tokens[3:]]
        assert all(0 < value < full and not (value & 1) for value in words)
        key = (k, tuple(tokens[3:]))
        assert key not in seen
        seen.add(key)
        root_present |= k == 18 and sorted(words) == initial
        memo_states += 1
        remaining[k] += 1
print(json.dumps({
    'verdict': 'PASS', 'profile_lower_bounds_all_match_signed_table': True,
    'rectangle_events': dict(events), 'rectangle_matrix_hits': dict(matrix_hits),
    'sampled_bank_histories_replayed': banks,
    'memo_header': 'PNP_COPY_MEMO_V1 0 19 oredge 1', 'memo_states': memo_states,
    'memo_remaining_budgets': dict(remaining), 'root_in_completed_memo': root_present,
    'limitations': [
        'Recorded root costs are checked arithmetically, not recomputed as rectangle maxima here.',
        'These are full emitted rectangle/bank traces, not a complete recursion DAG.',
        'Completed-only memo insertion follows the reviewed search source; no Lean proof is asserted.',
        'No UNSAT claim is inferred from a timeout or other limit.'
    ]}, indent=2))
