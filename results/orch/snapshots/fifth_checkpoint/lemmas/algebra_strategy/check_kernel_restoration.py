#!/usr/bin/env python3
"""Exact internal-wire OR-insertion census for the four-owner kernel.

The joint override condition is sufficient, not necessary.  Inputs are raw10
followed by the three correlated opposite-edge OR features.  All truth tables
are packed Python integers; every raw assignment is checked.
"""

import argparse
import itertools
import json
from pathlib import Path


def patterns(n):
    count = 1 << n
    return [sum(1 << mask for mask in range(count) if (mask >> i) & 1)
            for i in range(n)]


def evaluate(gates, inputs, output, forced=()):
    ones = (1 << (1 << 10)) - 1
    forced = set(forced)
    wires = [ones if i in forced else value for i, value in enumerate(inputs)]
    for op, a, b in gates:
        assert op in (0, 1)
        assert 0 <= a < len(wires) and 0 <= b < len(wires)
        value = (wires[a] & wires[b]) if op == 0 else (wires[a] | wires[b])
        wires.append(ones if len(wires) in forced else value)
    return wires[output]


def restore(gates, output, taps):
    """New input order: raw10, free features3, private lines by owner4."""
    new = []
    mapping = {}
    owner = {wire: p for p, wire in enumerate(taps)}
    assert len(owner) == 4
    for wire in range(13):
        mapping[wire] = wire
        if wire in owner:
            mapping[wire] = 17 + len(new)
            new.append([1, wire, 13 + owner[wire]])
    for j, (op, a, b) in enumerate(gates):
        wire = 13 + j
        mapping[wire] = 17 + len(new)
        new.append([op, mapping[a], mapping[b]])
        if wire in owner:
            old = mapping[wire]
            mapping[wire] = 17 + len(new)
            new.append([1, old, 13 + owner[wire]])
    return new, mapping[output]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--gates', type=Path, required=True)
    parser.add_argument('--case', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    case = json.loads(args.case.read_text())
    data = json.loads(args.gates.read_text())
    gates = data['gates'] if isinstance(data, dict) else data
    output = data.get('output', 13 + len(gates) - 1) if isinstance(data, dict) else 13 + len(gates) - 1
    assert case['raw_inputs'] == 10 and case['inputs'] == 13
    raw = patterns(10)
    inputs = raw + [0] * 3
    for i, feature in enumerate(case['features']):
        for j in feature['raw_indices']:
            inputs[10 + i] |= raw[j]
    target = 0
    for a, b in case['edges']:
        target |= raw[a] & raw[b]
    result = {'kernel_gates': len(gates), 'kernel_output': output,
              'kernel_exact': evaluate(gates, inputs, output) == target,
              'raw_assignments_per_override': 1024,
              'condition': 'all16 joint override masks, output=F OR selected point inputs',
              'sufficiency_only': True}
    if not result['kernel_exact']:
        args.out.write_text(json.dumps(result, indent=2) + '\n')
        print('Kernel is not exact; restoration census skipped.')
        return
    candidates = []
    for p in range(4):
        candidates.append([wire for wire in range(13 + len(gates))
                           if evaluate(gates, inputs, output, [wire]) == (target | raw[p])])
    result['single_override_candidates_by_owner'] = candidates
    tested = 0
    witnesses = []
    for taps in itertools.product(*candidates):
        if len(set(taps)) != 4:
            continue
        tested += 1
        valid = True
        for mask in range(16):
            forced = [taps[p] for p in range(4) if (mask >> p) & 1]
            expected = target
            for p in range(4):
                if (mask >> p) & 1:
                    expected |= raw[p]
            if evaluate(gates, inputs, output, forced) != expected:
                valid = False
                break
        if valid:
            new, new_output = restore(gates, output, taps)
            raw14 = patterns(14)
            new_inputs = raw14[:10] + [0] * 3 + raw14[10:]
            for i, feature in enumerate(case['features']):
                for j in feature['raw_indices']:
                    new_inputs[10 + i] |= raw14[j]
            expected14 = 0
            for a, b in case['edges']:
                expected14 |= raw14[a] & raw14[b]
            for p in range(4):
                expected14 |= raw14[p] & raw14[10 + p]
            wires = new_inputs[:]
            for op, a, b in new:
                wires.append((wires[a] & wires[b]) if op == 0 else (wires[a] | wires[b]))
            assert wires[new_output] == expected14
            witnesses.append({'taps_by_owner': list(taps), 'gates': new, 'output': new_output,
                              'inputs': 17, 'size': len(new), 'full_assignments_verified': 16384})
            break
    result['tap_tuples_tested'] = tested
    result['restoration_witnesses'] = witnesses
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'restoration_witnesses'}, indent=2))
    print('Joint restoration witnesses:', len(witnesses))


if __name__ == '__main__':
    main()
