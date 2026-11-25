import argparse
import itertools
import json
from pathlib import Path

from global_synthesis import evaluate
from subset_cegis import stamp


def truth_columns(case):
    size = 1 << case['raw_inputs']
    raw = [sum(1 << mask for mask in range(size) if mask >> i & 1)
           for i in range(case['raw_inputs'])]
    features = []
    for feature in case['features']:
        bits = 0
        for i in feature['raw_indices']:
            bits |= raw[i]
        features.append(bits)
    return raw + features, (1 << size) - 1


def evaluate_columns(gates, columns, ones, overrides=()):
    chosen = set(overrides)
    wires = [ones if i in chosen else value for i, value in enumerate(columns)]
    for op, a, b in gates:
        value = (wires[a] | wires[b]) if op else (wires[a] & wires[b])
        wires.append(ones if len(wires) in chosen else value)
    return wires[-1]


def restoration_candidates(case, gates):
    columns, ones = truth_columns(case)
    expected = 0
    for a, b in case['edges']:
        expected |= columns[a] & columns[b]
    assert evaluate_columns(gates, columns, ones) == expected
    owners = sorted(set(a for a, _ in case['edges']))
    single = [[wire for wire in range(len(columns) + len(gates))
               if evaluate_columns(gates, columns, ones, [wire]) == expected | columns[owner]]
              for owner in owners]
    stamp('SINGLE OVERRIDE CANDIDATES', single)
    for taps in itertools.product(*single):
        if len(set(taps)) != len(taps):
            continue
        valid = True
        for subset in range(1 << len(owners)):
            desired = expected
            active = []
            for i, owner in enumerate(owners):
                if subset >> i & 1:
                    desired |= columns[owner]
                    active.append(taps[i])
            if evaluate_columns(gates, columns, ones, active) != desired:
                valid = False
                break
        if valid:
            yield owners, list(taps)


def restore_full(kernel, full_case, gates, owners, taps):
    original = kernel['input_original']
    available = list(original)
    for feature in kernel['features']:
        lines = {original[i] for i in feature['raw_indices']}
        matches = [f['outside_wire'] for f in full_case['features']
                   if set(f['original_lines']) == lines]
        assert matches, lines
        available.append(matches[0])
    private = []
    full_original = full_case['input_original']
    for owner in owners:
        original_owner = original[owner]
        full_neighbors = {full_original[b] for a, b in full_case['edges']
                          if full_original[a] == original_owner}
        kernel_neighbors = {original[b] for a, b in kernel['edges'] if a == owner}
        difference = full_neighbors - kernel_neighbors
        assert len(difference) == 1
        private.append(next(iter(difference)))
    insertion = dict(zip(taps, private))
    answer = [list(gate) for gate in full_case['outside_gates']]
    mapping = []
    for i, wire in enumerate(available):
        if i in insertion:
            answer.append([1, wire, insertion[i]])
            wire = 26 + len(answer) - 1
        mapping.append(wire)
    for op, a, b in gates:
        logical_wire = len(mapping)
        answer.append([op, mapping[a], mapping[b]])
        wire = 26 + len(answer) - 1
        if logical_wire in insertion:
            answer.append([1, wire, insertion[logical_wire]])
            wire = 26 + len(answer) - 1
        mapping.append(wire)
    answer.append([1, full_case['outside_output'], mapping[-1]])
    assert len(answer) == len(full_case['outside_gates']) + len(gates) + len(taps) + 1
    return answer


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('candidate', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    folder = Path(__file__).resolve().parents[2] / 'circuit_search'
    kernel = json.loads((folder / 'four-owner-private-zero-kernel.json').read_text())
    full_case = json.loads((folder / 'four-owner-gadgets.json').read_text())[0]
    candidate = json.loads(args.candidate.read_text())
    if isinstance(candidate, list):
        gates = candidate
    else:
        gates = candidate.get('gates_list', candidate.get('gates'))
    assert isinstance(gates, list)
    for owners, taps in restoration_candidates(kernel, gates):
        full = restore_full(kernel, full_case, gates, owners, taps)
        geometry = json.loads((folder / 'geometry.json').read_text())
        tests = [((1 << a) | (1 << b), True) for a, b in geometry['edges']]
        tests += [(a | (b << 13), False) for a, b in geometry['maximal_independent_sets']]
        assert all(evaluate(full, mask, 26) == label for mask, label in tests)
        report = dict(gates=full, size=len(full), exact_witness=len(full) <= 63,
                      kernel_gates=gates, taps=taps, owners=owners,
                      simultaneous_override_cases=(1 << len(owners)) * (1 << kernel['raw_inputs']),
                      full_boundary_cases=len(tests))
        args.output.write_text(json.dumps(report))
        stamp('RESTORED EXACT FULL CIRCUIT', len(full), 'gates', 'taps', taps)
        break
    else:
        args.output.write_text(json.dumps(dict(restorable_by_this_criterion=False,
                                              kernel_gates=gates)))
        stamp('NO SIMULTANEOUS FOUR TAP RESTORATION')


if __name__ == '__main__':
    main()
