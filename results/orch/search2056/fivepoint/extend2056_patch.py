import argparse
import json
from pathlib import Path


def variable_tables(n):
    size = 1 << n
    result = []
    for i in range(n):
        run = 1 << i
        value = ((1 << run) - 1) << run
        width = 2 * run
        while width < size:
            value |= value << width
            width *= 2
        result.append(value)
    return result


def verified_patch(case, gates):
    n = case['ninputs']
    if not 1 <= len(gates) <= 24:
        raise ValueError('Expected a patch with at most24 gates')
    values = variable_tables(n)
    inputs = values[:]
    for j, gate in enumerate(gates):
        if len(gate) != 3:
            raise ValueError('A gate must have exactly three integer fields')
        op, a, b = gate
        if op not in (0, 1) or not 0 <= a < n + j or not 0 <= b < n + j:
            raise ValueError('Invalid binary monotone gate or forward reference')
        values.append((values[a] | values[b]) if op else (values[a] & values[b]))
    target = 0
    for row in case['positive']:
        endpoints = [i for i in range(n) if row & (1 << i)]
        if len(endpoints) != 2:
            raise ValueError('Positive row is not an edge')
        target |= inputs[endpoints[0]] & inputs[endpoints[1]]
    errors = (values[-1] ^ target).bit_count()
    if errors:
        raise ValueError(f'Patch fails exhaustive verification on {errors} assignments')
    return 1 << n


def extend(case, gates):
    n = case['ninputs']
    names = case['points'] + [13 + l for l in case['lines']]
    if len(names) != n:
        raise ValueError('Input map length mismatch')
    def lift(w):
        return names[w] if w < n else 26 + w - n
    result = [[op, lift(a), lift(b)] for op, a, b in gates]
    roots = [26 + len(result) - 1]
    selected = set(case['points'])
    for p in range(13):
        if p in selected:
            continue
        lines = [13 + l for l in range(13) if (p + l) % 13 in (0, 1, 3, 9)]
        if len(lines) != 4:
            raise ValueError('Incorrect line degree')
        value = lines[0]
        for line in lines[1:]:
            wire = 26 + len(result)
            result.append([1, value, line])
            value = wire
        wire = 26 + len(result)
        result.append([0, p, value])
        roots.append(wire)
    output = roots[0]
    for root in roots[1:]:
        wire = 26 + len(result)
        result.append([1, output, root])
        output = wire
    if len(result) != len(gates) + 40 or output != 26 + len(result) - 1:
        raise ValueError('Extension size accounting failed')
    return result, output


def main():
    parser = argparse.ArgumentParser(description='Verify and extend a five-point plane2056 patch')
    parser.add_argument('--cases', required=True, type=Path)
    parser.add_argument('--candidate', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    cases = json.loads(args.cases.read_text())
    candidate = json.loads(args.candidate.read_text())
    index = candidate['case']
    if not isinstance(index, int) or not 0 <= index < len(cases):
        raise ValueError('Invalid case index')
    case = cases[index]
    gates = candidate['gates']
    checked = verified_patch(case, gates)
    full, output = extend(case, gates)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    document = {'case': index, 'points': case['points'], 'lines': case['lines'],
                'patch_gates': len(gates), 'patch_assignments_verified': checked,
                'gates': full, 'output': output, 'size': len(full),
                'status': 'control only' if len(full) > 63 else 'candidate requires Lean checking'}
    args.output.write_text(json.dumps(document, indent=2) + '\n')
    args.output.with_suffix('.txt').write_text(''.join(f'{op} {a} {b}\n' for op, a, b in full))
    print(f'PASS patch all {checked} assignments; extended to {len(full)} gates')


if __name__ == '__main__':
    main()
