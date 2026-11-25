import argparse
import json
from pathlib import Path
from repair_neighborhood import normalize_gates, edit_distance


def simplify(gates, ninputs):
    mapping = {i: i for i in range(ninputs)}
    reduced = []
    seen = {}
    for i, (op, a, b) in enumerate(gates):
        a, b = sorted((mapping[a], mapping[b]))
        if a == b:
            wire = a
        elif (op, a, b) in seen:
            wire = seen[(op, a, b)]
        else:
            wire = ninputs + len(reduced)
            reduced.append([op, a, b])
            seen[(op, a, b)] = wire
        mapping[ninputs + i] = wire
    output = mapping[ninputs + len(gates) - 1]
    needed = set()
    pending = [output]
    while pending:
        wire = pending.pop()
        if wire < ninputs or wire in needed:
            continue
        needed.add(wire)
        _, a, b = reduced[wire - ninputs]
        pending.extend((a, b))
    compact = []
    remap = {i: i for i in range(ninputs)}
    for i, (op, a, b) in enumerate(reduced):
        if ninputs + i not in needed:
            continue
        remap[ninputs + i] = ninputs + len(compact)
        compact.append([op, *sorted((remap[a], remap[b]))])
    wire = remap[output]
    genuine = len(compact)
    while len(compact) < len(gates):
        compact.append(['or', wire, wire])
        wire = ninputs + len(compact) - 1
    return compact, genuine


def check(gates, ninputs, edges):
    assert all(op in ('and', 'or') and 0 <= a <= b < ninputs + i
               for i, (op, a, b) in enumerate(gates))
    for mask in range(1 << ninputs):
        values = [bool(mask >> i & 1) for i in range(ninputs)]
        for op, a, b in gates:
            values.append(values[a] or values[b] if op == 'or' else values[a] and values[b])
        expected = any(mask >> a & 1 and mask >> b & 1 for a, b in edges)
        assert values[-1] == expected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--mapping', type=Path, required=True)
    parser.add_argument('--witness', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    metadata = json.loads(args.mapping.read_text())
    gates = normalize_gates(json.loads(args.witness.read_text()))
    assert len(gates) == metadata['gates']
    distance = None
    if 'repair' in metadata:
        distance = edit_distance(metadata['repair']['seed'], gates)
        assert distance <= metadata['repair']['budget']
    check(gates, metadata['ninputs'], metadata['edges'])
    normalized, genuine = simplify(gates, metadata['ninputs'])
    assert genuine >= 2
    assert all(a < b for _, a, b in normalized[:2])
    check(normalized, metadata['ninputs'], metadata['edges'])
    args.output.write_text(json.dumps(normalized, indent=2) + '\n')
    print(json.dumps({'original_gates': len(gates), 'genuine_gates': genuine,
                      'padded_gates': len(normalized), 'verified_inputs': 1 << metadata['ninputs'],
                      'original_repair_distance': distance,
                      'initial_fanins_distinct': True, 'output': str(args.output)}))


if __name__ == '__main__':
    main()
