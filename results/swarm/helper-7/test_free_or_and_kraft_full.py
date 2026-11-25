"""Finite arithmetic, fixed-circuit, scope and legacy-byte checks; no target search."""
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import free_or_and_query as q
from test_free_or_and_kraft import explicit_values

ROOT = Path(__file__).resolve().parent


LEGACY_FINGERPRINTS = {'["H12",false,0]': '2e710bef933033096eda47a2836cba5321df5cbd48e4a57532df1ca339def59e',
 '["H12",false,5]': '373bc266770ba6f96d4d6fc91df76fc00e08ece7b9e4e0eb6dc4278a96547d42',
 '["H12",false,null]': 'b46c197c27d14b8fdb9bf88d9d00a87eadebe23a7b4c50ad3d98633e30e2c4c5',
 '["H12",true,0]': 'e58b92207874048e2acd4302403506a719919e4a9ff285ebf8be65de1974413c',
 '["H12",true,5]': '7a1f0e0fc70411ed89f96cbd42bb676abcb8fc4a719276b936ca7c8a7f1b27d8',
 '["H12",true,null]': '0aad22962c07874f0bbaef44a78e7aefdd20ccc9de4a4bc90a4a363a72a0550b',
 '["edge0",false,0]': '1168ef0c7d0b7b5d9926ff1ad9e8362e2bb1a6d2bd60895d972de71149b5c573',
 '["edge0",false,5]': '25990d776e26628065411a160031a9d8c90afd188aa45a7667bdeb8584301eb1',
 '["edge0",false,null]': 'cef9abba0579fae2d718ad1b211a3baf288ca2e7e63281c41e07be8f96177169',
 '["edge0",true,0]': 'ed0813439d8c9adff18c54cc35dbbbd0cde4e891b50e6bfe85e1f82d9e494b16',
 '["edge0",true,5]': '239550f4f7e8482106505e8435839e4d9bebdfb3f9ada2ed68e70f489ff7d726',
 '["edge0",true,null]': '691f4631e7d3cce4ad08dcc4e47f80b21c4fd7a2746f4121761c07f58122439c',
 '["edge2",false,0]': '44954caf9b95efafe17ab70251d862c148489719ef466ef401fb33db3fff8b2a',
 '["edge2",false,5]': '01b7e116ad8eb8d5fbd287a0119411fb4ebf0ea623811a8ab3e0feae5f70f60d',
 '["edge2",false,null]': '8efd4630cada27d5185f4abd5282f562d59da6b37851d9c0c2c54a0e4762a320',
 '["edge2",true,0]': '802fe0fab31883bd4b7ba32aa6802c17311aa63efab42425ad867791b9f69bb9',
 '["edge2",true,5]': '2c094b30a4b59a5302a7452d8d43379dd6592dfdbb403259afd16da1654d4c54',
 '["edge2",true,null]': 'a82d95938cf61fff39be40699efb982176ddb446f1e6bfa549a5ffe6e0662bc9',
 '["empty",false,0]': 'bd3adb9fe3d4b2e4a64a89ab6e78dbe7aca917c35d03a2d6223c686b441ca9dc',
 '["empty",false,5]': 'e93c830465467d8792fd98d104389a020bb9e719ba48b4b0624070c87461c7d0',
 '["empty",false,null]': 'ae65186fca824c572a4f17c0b8b8a77979e753b6e7ab75bb94ce3b76ec337e7f',
 '["empty",true,0]': '11b81b54a6fe81692e3e114fd91cf48135a4dd414bb8df62bd7b6448b74825dd',
 '["empty",true,5]': '861d8602328dbc507fc85cf40c26bc1c2f4d435d9ebf5ca3fb192c7053d2a990',
 '["empty",true,null]': '55b88c239438af0b3fba6effe84a5dac7169f108e8a8a20a78641ce95e155e0b'}


def arithmetic():
    commands = ['(set-logic QF_BV)', '(set-option :timeout 30000)']
    wrong = []
    cases = 0
    linear_only_examples = []
    for k in range(5):
        for m in range(1, 5):
            for counts in itertools.product(range(k + 1), repeat=m):
                fragment = []
                for i in range(k):
                    different = sum(1 << r for r, count in enumerate(counts) if i >= count)
                    fragment.append(f'(define-fun kraft_diff{i} () (_ BitVec {m}) (_ bv{different} {m}))')
                width = q.append_full_kraft(fragment, k, list(range(m)))
                bound = fragment.pop()
                assert bound.startswith('(assert ') and bound.endswith(')')
                predicate = bound[len('(assert '):-1]
                expected = sum(1 << c for c in counts)
                assert expected <= m * (1 << k) < (1 << width)
                assert k < width
                prefix = f'c{cases}_kraft_'
                commands.extend(item.replace('kraft_', prefix) for item in fragment)
                total = prefix + 'full_total'
                wrong.append(f'(not (= {total} (_ bv{expected} {width})))')
                expected_predicate = str(expected <= (1 << k)).lower()
                wrong.append(f'(not (= {predicate.replace("kraft_", prefix)} {expected_predicate}))')
                if sum(counts) <= (1 << k) - m and expected > (1 << k):
                    linear_only_examples.append([k, m, list(counts), expected])
                cases += 1
    assert linear_only_examples
    commands += ['(assert (or ' + ' '.join(wrong) + '))', '(check-sat)']
    result = q.solve('\n'.join(commands) + '\n', [])
    assert result['status'] == 'unsat', result
    return {'arithmetic_vectors': cases, 'strict_strength_example': linear_only_examples[0]}


def fixed():
    square = [(0, 2), (0, 3), (1, 2), (1, 3)]
    cases = [
        ('edge', 2, [(0, 1)], [([0], [1])], [2]),
        ('square', 4, square, [([0, 1], [2, 3])], [4]),
        ('false_padding', 4, square, [([], []), ([0, 1], [2, 3])], [4, 5]),
        ('dead_AND', 4, square, [([0], [1]), ([0, 1], [2, 3])], [5]),
        ('shared_OR', 4, square, [([0, 1], [2]), ([0, 1], [3])], [4, 5]),
        ('empty_boundary', 1, [], [], []),
    ]
    fixture = json.loads((ROOT / 'graphs' / 'C6book3.json').read_text())
    n, edges, cover = fixture['n'], fixture['edges'], [0, 3, 5, 7, 9, 11, 13]
    neighbors = {v: [] for v in cover}
    for u, v in edges:
        owner = u if u in neighbors else v
        assert owner in neighbors
        neighbors[owner].append(v if owner == u else u)
    gates = []
    for v in cover:
        left, right = [v], sorted(neighbors[v])
        if sum(1 << j for j in left) > sum(1 << j for j in right):
            left, right = right, left
        gates.append((left, right))
    gates.sort(key=lambda gate: (max(gate[0] + gate[1]) + 1,
                                sum(1 << j for j in gate[0]),
                                sum(1 << j for j in gate[1])))
    cases.append(('C6book3_fixed_standard7', n, edges, gates, list(range(n, n + 7))))
    reports = []
    for linear in [False, True]:
        for name, n, edges, gates, out in cases:
            source, meta = q.generate(n, edges, len(gates), timeout_ms=5000,
                                      and_kraft=linear, and_kraft_full=True)
            values = explicit_values(meta, gates, out)
            q.validate_selected_model(meta, values)
            counts = q.equal_operand_counts(meta, values)
            pin = '\n'.join(f'(assert (= {key} {str(value).lower()}))' for key, value in values.items())
            pinned = source.replace('(check-sat)', pin + '\n(check-sat)')
            result = q.solve(pinned, meta['selectors'])
            assert result['status'] == 'sat' and result['selectors'] == values
            width = meta['and_kraft_full_accumulator_width']
            contrary = f'(assert (not (= kraft_full_total (_ bv{counts["exponential_total"]} {width}))))'
            assert q.solve(pinned.replace('(check-sat)', contrary + '\n(check-sat)'), [])['status'] == 'unsat'
            if edges:
                circuit = q.reconstruct(meta, values)
                assert circuit['exhaustively_checked_inputs'] == (1 << n)
            else:
                try:
                    q.reconstruct(meta, values)
                except ValueError as error:
                    assert 'at least one edge' in str(error)
                else:
                    raise AssertionError('empty graph reconstruction did not reject')
            reports.append({'name': name, 'linear_enabled': linear, **counts})
        source, meta = q.generate(2, [(0, 1)], 0, timeout_ms=5000,
                                  and_kraft=linear, and_kraft_full=True)
        assert q.solve(source, meta['selectors'])['status'] == 'unsat'
    return reports


def scope_and_legacy():
    # Frozen SHA-256 of [source, metadata] from the reviewed linear-only generator.
    # These cover both linear flag values and three cap settings without an old encoder.
    expected = LEGACY_FINGERPRINTS
    checked = 0
    for name, n, edges, k in [('H12', 12, q.H12_EDGES, 5), ('empty', 1, [], 0),
                             ('edge0', 2, [(0, 1)], 0), ('edge2', 2, [(0, 1)], 2)]:
        for linear in [False, True]:
            for cap in [None, 0, 5]:
                pair = q.generate(n, edges, k, private_or_cap=cap, and_kraft=linear)
                key = json.dumps([name, linear, cap], separators=(',', ':'))
                digest = hashlib.sha256(json.dumps(pair, sort_keys=True).encode()).hexdigest()
                assert digest == expected[key]
                checked += 1
    assert checked == len(expected) == 24
    with tempfile.TemporaryDirectory(prefix='free-or-scope-') as directory:
        root = Path(directory)
        fixture, smt, result = root / 'empty.json', root / 'empty.smt2', root / 'empty-result.json'
        fixture.write_text(json.dumps({'name': 'empty', 'n': 1, 'edges': []}))
        proc = subprocess.run([sys.executable, str(ROOT / 'free_or_and_query.py'),
                               '--fixture', str(fixture), '--and-cap', '0', '--and-kraft-full',
                               '--smt-out', str(smt), '--result-out', str(result), '--solve'],
                              capture_output=True, text=True)
        assert proc.returncode == 2
        assert 'must describe a graph with at least one edge' in proc.stderr
        assert proc.stdout == '' and not smt.exists() and not result.exists()
    return {'legacy_encodings_and_metadata_unchanged': 24,
            'empty_graph_CLI_rejected_before_outputs': True,
            'empty_graph_low_level_arithmetic_preserved': True}


def main():
    report = {**arithmetic(), 'fixed_cases': fixed(), **scope_and_legacy(),
              'target_synthesis_run': False}
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
