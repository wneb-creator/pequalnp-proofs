"""Tiny solver checks and fixed-model Kraft arithmetic; no target synthesis run."""

import hashlib
import json
from pathlib import Path

import free_or_and_query as q


def explicit_values(meta, gates, output):
    values = dict.fromkeys(meta['selectors'], False)
    for i, (left, right) in enumerate(gates):
        for j in left:
            values[f'l{i}_{j}'] = True
        for j in right:
            values[f'r{i}_{j}'] = True
    for j in output:
        values[f'out_{j}'] = True
    return values


def independent_counts(meta, values):
    # Compute one bit-vector per source, then XOR the OR operands. This does
    # not use the implementation's rowwise equal_operand_counts helper.
    negatives = meta['negative_rows']
    mask = (1 << len(negatives)) - 1
    source = [sum(1 << r for r, assignment in enumerate(negatives)
                  if assignment & (1 << v)) for v in range(meta['n'])]
    equal_total = 0
    for i in range(meta['and_cap']):
        operands = []
        for side in ['l', 'r']:
            value = 0
            for j, vector in enumerate(source):
                if values[f'{side}{i}_{j}']:
                    value |= vector
            operands.append(value)
        left, right = operands
        equal_total += (mask ^ (left ^ right)).bit_count()
        source.append(left & right)
    return equal_total


def check_fixed_model(source, meta, values):
    counts = q.equal_operand_counts(meta, values)
    assert counts['equal_total'] == independent_counts(meta, values)
    assert counts['equal_total'] <= counts['linear_budget']
    assert counts['exponential_total'] <= counts['exponential_budget']
    pin = '\n'.join('(assert (= ' + name + ' ' + str(value).lower() + '))'
                    for name, value in values.items())
    assert source.count('(check-sat)') == 1
    pinned = source.replace('(check-sat)', pin + '\n(check-sat)')
    result = q.solve(pinned, meta['selectors'])
    assert result['status'] == 'sat' and result['selectors'] == values
    width = max(1, max(meta['and_cap'] * len(meta['negative_rows']),
                       counts['linear_budget']).bit_length())
    disagree = '(assert (not (= kraft_equal_total (_ bv' + str(counts['equal_total'])
    disagree += ' ' + str(width) + '))))'
    wrong = pinned.replace('(check-sat)', disagree + '\n(check-sat)')
    assert q.solve(wrong, meta['selectors'])['status'] == 'unsat'
    return counts


def main():
    reports = []
    source, _ = q.generate(12, q.H12_EDGES, 5)
    assert hashlib.sha256(source.encode()).hexdigest() == q.H12_SHA256
    # New flag must not alter old generation when absent, even metadata shape.
    for name, n, edges, private in [
        ('edge', 2, [(0, 1)], 0),
        ('star', 3, [(0, 1), (0, 2)], 1),
        ('square', 4, [(0, 2), (0, 3), (1, 2), (1, 3)], 2),
    ]:
        source, meta = q.generate(n, edges, 1, timeout_ms=5000,
                                  private_or_cap=private, and_kraft=True)
        solved = q.solve(source, meta['selectors'])
        assert solved['status'] == 'sat'
        counts = check_fixed_model(source, meta, solved['selectors'])
        circuit = q.reconstruct(meta, solved['selectors'])
        assert counts['equal_total'] == counts['linear_budget'] == 0
        reports.append({'name': name, 'size': circuit['size'], **counts})

    square = [(0, 2), (0, 3), (1, 2), (1, 3)]
    source, meta = q.generate(4, square, 2, timeout_ms=5000, and_kraft=True)
    for name, gates, output in [
        ('false_padding', [([], []), ([0, 1], [2, 3])], [4, 5]),
        ('dead_AND', [([0], [1]), ([0, 1], [2, 3])], [5]),
        ('shared_OR', [([0, 1], [2]), ([0, 1], [3])], [4, 5]),
    ]:
        values = explicit_values(meta, gates, output)
        counts = check_fixed_model(source, meta, values)
        q.reconstruct(meta, values)
        reports.append({'name': name, **counts})
    assert reports[3]['equal_total'] == 2

    source, meta = q.generate(2, [(0, 1)], 0, timeout_ms=5000, and_kraft=True)
    assert meta['and_kraft_equal_budget'] == -1 and '(assert false)' in source
    assert q.solve(source, meta['selectors'])['status'] == 'unsat'
    source, meta = q.generate(1, [], 0, timeout_ms=5000, and_kraft=True)
    empty_values = dict.fromkeys(meta['selectors'], False)
    zero_counts = check_fixed_model(source, meta, empty_values)
    assert zero_counts['equal_total'] == zero_counts['linear_budget'] == 0

    fixture = json.loads((Path(__file__).parent / 'graphs' / 'C6book3.json').read_text())
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
    source, meta = q.generate(n, edges, 7, timeout_ms=5000,
                              private_or_cap=15, and_kraft=True)
    values = explicit_values(meta, gates, list(range(n, n + 7)))
    counts = check_fixed_model(source, meta, values)
    circuit = q.reconstruct(meta, values)
    assert circuit['size'] == 22 and circuit['and_count'] == 7 and circuit['or_count'] == 15
    assert circuit['exhaustively_checked_inputs'] == 16384
    reports.append({'name': 'C6book3_fixed_standard7', 'size': circuit['size'], **counts})
    print(json.dumps({'no_option_h12_hash': q.H12_SHA256,
                      'checks': reports, 'M_exceeds_capacity_contradiction': True,
                      'zero_AND_zero_budget_checked': True,
                      'target_synthesis_run': False}, indent=2))


if __name__ == '__main__':
    main()
