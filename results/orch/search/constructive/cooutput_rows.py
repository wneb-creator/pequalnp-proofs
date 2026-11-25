import argparse
import json
from pathlib import Path


EDGES = [
    (0, 7), (0, 8), (0, 10), (1, 7), (1, 9),
    (2, 8), (2, 12), (3, 7), (3, 11), (3, 12),
    (4, 10), (4, 11), (5, 9), (5, 10), (5, 12),
    (6, 8), (6, 9), (6, 11),
]
LINEAR = (1, 2, 4)
LINEAR_MASK = sum(1 << v for v in LINEAR)
ALL_MASK = (1 << 13) - 1


def independent(mask):
    return not any(mask & (1 << a) and mask & (1 << b) for a, b in EDGES)


def maximal_independent(allowed):
    result = []
    for mask in range(1 << 13):
        if mask & ~allowed or not independent(mask):
            continue
        if all(not independent(mask | (1 << v))
               for v in range(13) if allowed & (1 << v) and not mask & (1 << v)):
            result.append(mask)
    return result


def seed(missing, prefix):
    # The posted prefix is existential and normalized under automorphisms.
    # These are two seed families, not distinct format requirements.
    if prefix == 'independent':
        gates = [[1, 0, 1], [1, 0, 2], [1, 1, 2], [1, 4, 15]]
        w = 16
    else:
        assert prefix == 'a-first'
        gates = [[1, 1, 2], [1, 4, 13]]
        w = 14
    terms = []
    for right in range(7, 13):
        neighbors = [a for a, b in EDGES if b == right and (a, b) != missing]
        if prefix == 'independent' and right == 7:
            assert neighbors == [0, 1, 3]
            wire, remaining = 13, [3]
        elif prefix == 'independent' and right == 8:
            assert neighbors == [0, 2, 6]
            wire, remaining = 14, [6]
        else:
            wire, remaining = neighbors[0], neighbors[1:]
        for left in remaining:
            gates.append([1, wire, left])
            wire = 12 + len(gates)
        gates.append([0, wire, right])
        terms.append(12 + len(gates))
    output = terms[0]
    for term in terms[1:]:
        gates.append([1, output, term])
        output = 12 + len(gates)
    assert len(gates) == 24
    errors = []
    for mask in range(1 << 13):
        values = [bool(mask & (1 << v)) for v in range(13)]
        for op, a, b in gates:
            assert 0 <= a < len(values) and 0 <= b < len(values)
            values.append((values[a] or values[b]) if op else (values[a] and values[b]))
        target = not independent(mask)
        linear = bool(mask & LINEAR_MASK)
        assert values[w] == linear
        expected = any((a, b) != missing and values[a] and values[b] for a, b in EDGES)
        assert values[output] == expected
        if values[output] != target:
            errors.append(mask)
    return dict(inputs=13, gates=gates, f0_output=output, w_output=w, prefix_kind=prefix,
                missing_edge=list(missing), exact_a=True, f0_error_count=len(errors),
                first_f0_error=errors[0])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', required=True)
    args = parser.parse_args()
    output_dir = Path(args.output_dir)
    f0_zero = maximal_independent(ALL_MASK)
    w_zero = maximal_independent(ALL_MASK ^ LINEAR_MASK)
    f0_one = sorted((1 << a) | (1 << b) for a, b in EDGES)
    w_one = [1 << v for v in LINEAR]
    rows = {}

    def constrain(mask, key, value):
        row = rows.setdefault(mask, dict(mask=mask))
        assert key not in row or row[key] == value
        row[key] = value

    for mask in f0_one:
        constrain(mask, 'f0', 1)
    for mask in f0_zero:
        constrain(mask, 'f0', 0)
    for mask in w_one:
        constrain(mask, 'w', 1)
    for mask in w_zero:
        constrain(mask, 'w', 0)

    # Fill additional correct consequences on rows already present, without adding rows.
    for mask, row in rows.items():
        constrain(mask, 'f0', int(not independent(mask)))
        if mask & LINEAR_MASK:
            constrain(mask, 'w', 1)
        elif independent(mask):
            constrain(mask, 'w', 0)

    # Independently certify sufficiency of every boundary family by direct containment.
    for mask in range(1 << 13):
        if independent(mask):
            assert any(mask & y == mask for y in f0_zero)
        else:
            assert any(x & mask == x for x in f0_one)
        if mask & LINEAR_MASK:
            assert any(x & mask == x for x in w_one)
        elif independent(mask):
            assert any(mask & y == mask for y in w_zero)

    result = dict(inputs=13, gate_budget=24, linear_vertices=list(LINEAR), edges=EDGES,
                  f0_positive_rows=f0_one, f0_negative_rows=f0_zero,
                  w_positive_rows=w_one, w_negative_rows=w_zero,
                  rows=[rows[m] for m in sorted(rows)],
                  full_assignment_coverage_checked=1 << 13)
    path = output_dir / 'cooutput24-boundary-rows.json'
    path.write_text(json.dumps(result, indent=2) + '\n')
    for missing, prefix in (((0, 10), 'independent'), ((1, 9), 'independent'),
                            ((0, 7), 'a-first'), ((1, 7), 'a-first')):
        data = seed(missing, prefix)
        path = output_dir / f'cooutput24-seed-missing-{missing[0]}-{missing[1]}.json'
        path.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps(dict(f0_positive_count=len(f0_one), f0_negative_count=len(f0_zero),
                          w_positive_count=len(w_one), w_negative_count=len(w_zero),
                          union_row_count=len(rows), checked_assignments=1 << 13,
                          seed_count=4)))


if __name__ == '__main__':
    main()
