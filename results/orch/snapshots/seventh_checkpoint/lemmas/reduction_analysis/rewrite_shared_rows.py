import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'lean_baseline/sat/full63_filtered_5extra_seed.json'
ROWS = [
    [13, 14, 16, 22], [13, 15, 21, 25], [14, 20, 24, 25],
    [13, 19, 23, 24], [18, 22, 23, 25], [17, 21, 22, 24],
    [16, 20, 21, 23], [15, 19, 20, 22], [14, 18, 19, 21],
    [13, 17, 18, 20], [16, 17, 19, 25], [15, 16, 18, 24],
    [14, 15, 17, 23],
]


def normalize(terms):
    result = []
    for term in sorted(set(terms), key=lambda term: (len(term), tuple(sorted(term)))):
        if not any(small <= term for small in result):
            result.append(term)
    return frozenset(result)


def forms(inputs, gates):
    wires = [frozenset([frozenset([i])]) for i in range(inputs)]
    for operation, left, right in gates:
        assert left < len(wires) and right < len(wires)
        if operation == 1:
            wires.append(normalize(wires[left] | wires[right]))
        else:
            assert operation == 0
            wires.append(normalize(a | b for a in wires[left] for b in wires[right]))
    return wires


def maximal_negatives():
    result = set()
    for mask in range(1 << 13):
        neighbors = {line for point in range(13) if mask >> point & 1 for line in ROWS[point]}
        points = [point for point in range(13) if set(ROWS[point]) <= neighbors]
        result.add(sum(1 << point for point in points)
                   + sum(1 << line for line in range(13, 26) if line not in neighbors))
    assert len(result) == 704
    return result


def main():
    old = json.loads(SOURCE.read_text())
    target = frozenset(frozenset([point, line])
                       for point in range(13) for line in ROWS[point])
    previous_four = forms(26, json.loads((HERE / 'full63_algebraic_4extra_seed.json').read_text()))[-1]
    negatives = maximal_negatives()
    reports = []
    for exact_second in [False, True]:
        gates = [list(gate) for gate in old[:3]]
        mapping = {i: i for i in range(29)}

        def emit(operation, left, right):
            gates.append([operation, left, right])
            return 26 + len(gates) - 1

        if exact_second:
            common = emit(1, 25, 28)
            left = emit(1, 13, 15)
            left = emit(1, left, common)
            left = emit(0, 1, left)
            right = emit(1, 14, 20)
            right = emit(1, right, common)
            right = emit(0, 2, right)
        else:
            common = emit(1, 27, 28)
            common = emit(1, 25, common)
            left = emit(1, 13, common)
            left = emit(0, 1, left)
            right = emit(1, 14, common)
            right = emit(0, 2, right)
        mapping[36] = emit(1, left, right)
        for index, (operation, left, right) in enumerate(old[11:], 11):
            mapping[26 + index] = emit(operation, mapping[left], mapping[right])

        output = forms(26, gates)[-1]
        extras = sorted(sorted(term) for term in output - target)
        assert target <= output and all(len(term) == 2 for term in output)
        assert len(extras) == (2 if exact_second else 4)
        if not exact_second:
            assert output == previous_four
        full_name = f'full{len(gates)}_shared_rows_{len(extras)}extra_seed.json'
        (HERE / full_name).write_text(json.dumps(gates, indent=2) + '\n')

        residual = [[operation, left - 1, right - 1] for operation, left, right in gates[:-2]]
        outputs = [gates[-1][1] - 1, gates[-2][2] - 1]
        residual_forms = forms(25, residual)
        assert residual_forms[outputs[1]] == frozenset(frozenset([i]) for i in [12, 13, 15, 21])
        active = set()
        pending = [outputs[0]]
        while pending:
            wire = pending.pop()
            if wire < 25 or wire in active:
                continue
            active.add(wire)
            pending.extend(residual[wire - 25][1:])
        residual_name = f'full_residual_shared_rows_{len(extras)}extra_joint{len(residual)}_seed.json'
        data = {
            'gates': residual, 'outputs': outputs, 'input_original': list(range(1, 26)),
            'extra_edges': [[left - 1, right - 1] for left, right in extras],
            'joint_size': len(residual), 'residual_size': len(active),
            'tap_is_correct': True, 'target_met': False,
            'and_count': sum(operation == 0 for operation, _, _ in residual),
            'verification': 'Exact antichain DNF; all desired edges present, only listed quadratic extras, exact Q.',
        }
        (HERE / residual_name).write_text(json.dumps(data, indent=2) + '\n')
        reports.append({
            'full_file': full_name, 'residual_file': residual_name,
            'gates': len(gates), 'and_count': sum(operation == 0 for operation, _, _ in gates),
            'extra_edges': extras, 'residual_size': len(active),
            'false_maximal_negative_inputs': sum(
                any((bits >> left & 1) and (bits >> right & 1) for left, right in extras)
                for bits in negatives),
        })
    (HERE / 'shared-rows-seed-rewrites.validation.json').write_text(json.dumps(reports, indent=2) + '\n')
    print(json.dumps(reports, indent=2))


if __name__ == '__main__':
    main()
