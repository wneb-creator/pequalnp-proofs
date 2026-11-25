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
assert meta['memo_input'] is not None and meta['mono_nine_bound'] == 15
assert '--memo-in' in meta['command'] and '--mono-nine15' in meta['command']
assert hashlib.sha256((p / 'rectangles-v5.txt').read_bytes()).hexdigest() == meta['matrix_sha256'] == 'e2c98359c0d903d5b439ec744de076267db30e674cb7e6d75d165337352e7f41'
lineage = json.loads((p / 'lineage.json').read_text())
assert lineage['input_run_metadata']['memo_input'] is not None
assert lineage['input_run_metadata']['mono_nine_bound'] == 15
assert lineage['input_memo_states'] == 61991
assert meta['input_memo_sha256'] == lineage['input_memo_sha256'] == '3cb7e8aca9aff0693264c265c1ef5a4677d0eb416ad73ef2e868ae754fbbebb3'
assert hashlib.sha256((p / 'input-weak15.memo').read_bytes()).hexdigest() == meta['input_memo_sha256']
with (p / 'input-weak15.memo').open() as stream:
    assert stream.readline().split() == ['PNP_COPY_MEMO_V1', '0', '19', 'oredge', '1']
    assert sum(1 for _ in stream) == 61991
assert meta['source_sha256'] == lineage['input_run_metadata']['source_sha256']
assert 'loaded completed memo states=61991 unique=61991' in (p / 'stdout.txt').read_text()
source = (p / 'copy_search_weak15.cpp').read_text()
assert hashlib.sha256(source.encode()).hexdigest() == meta['source_sha256'] == 'cad7cc15c9826879fc9968bc02c61e17c6fbddff279252cce887548d1c9bd35c'
assert lineage['input_run_metadata']['input_memo_sha256'] == '4124aa77228c73e08e3cdf2549313f032deda1a1bdff6c1cb767ca515a3c6645'
profiles = re.search(r'static const CP profiles\[CP_COUNT\]\s*=\s*\{(.*?)\};', source, re.S)
assert profiles
values = [tuple(map(int, v)) for v in re.findall(r'\{(\d+),(\d+),(\d+),(\d+)\}', profiles.group(1))]
assert len(values) == 1145
assert all((15 if i < 10 else mono) == signed for i, (_, _, mono, signed) in enumerate(values))

assert meta['exit_code'] == -6
assert 'std::bad_alloc' in (p / 'stderr.txt').read_text()
assert 'finished found=' not in (p / 'stdout.txt').read_text()
truncated_records = {}
events = Counter()
matrix_hits = Counter()
matrices = {}
referenced = set()
signals = {}
with (p / 'rectangles.jsonl').open() as stream:
    for line in stream:
        try:
            x = json.loads(line)
        except json.JSONDecodeError:
            assert stream.read() == ''
            truncated_records['rectangles.jsonl'] = {'bytes': len(line.encode()), 'sha256': hashlib.sha256(line.encode()).hexdigest()}
            break
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
assert events['header'] == 1 and events['matrix_loaded'] == 49
missing_signal_ids = referenced - signals.keys()
assert events['signal'] == 0  # Uncaught allocation failure prevented the final signal dictionary.
assert missing_signal_ids  # Record this limitation rather than claiming signature replay.

banks = 0
with (p / 'banks.jsonl').open() as stream:
    for line in stream:
        try:
            x = json.loads(line)
        except json.JSONDecodeError:
            assert stream.read() == ''
            truncated_records['banks.jsonl'] = {'bytes': len(line.encode()), 'sha256': hashlib.sha256(line.encode()).hexdigest()}
            break
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
root_orbit = {tuple(sorted(inputs + [inputs[a] | inputs[b]])) for a, b in edges}
root_orbit_present = False
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
        root_orbit_present |= k == 18 and tuple(sorted(words)) in root_orbit
        memo_states += 1
        remaining[k] += 1
assert memo_states == 76286
assert not root_orbit_present
print(json.dumps({
    'verdict': 'PASS_FOR_CHECKPOINT_AND_AVAILABLE_RECORDS', 'allocation_failure': True, 'truncated_final_records': truncated_records,
    'missing_signal_footer': True, 'unresolved_rectangle_signal_ids': len(missing_signal_ids),
    'all15_root_orbits_absent': not root_orbit_present, 'input_memo_states': 61991, 'source_unchanged_from_fresh_weak_run': True,
    'profile_lower_bounds_all_match_signed_table': True,
    'rectangle_events': dict(events), 'rectangle_matrix_hits': dict(matrix_hits),
    'sampled_bank_histories_replayed': banks,
    'memo_header': 'PNP_COPY_MEMO_V1 0 19 oredge 1', 'memo_states': memo_states,
    'new_completed_memo_states': memo_states - 61991,
    'memo_remaining_budgets': dict(remaining), 'root_in_completed_memo': root_present,
    'limitations': [
        'Recorded root costs are checked arithmetically only; rectangle IDs cannot all be resolved to truth signatures because the footer is absent.',
        'Preserved bytes contain available rectangle/bank records; allocation failure prevented the final signal dictionary. They are not a complete recursion DAG.',
        'Completed-only memo insertion follows the reviewed search source; no Lean proof is asserted.',
        'No UNSAT claim is inferred from a timeout or other limit.',
        'Input memo is the verified weak15 V3 continuation only; its states are recanonicalized by the unchanged loader.'
    ]}, indent=2))
