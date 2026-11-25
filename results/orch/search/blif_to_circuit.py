import argparse
import json
from pathlib import Path

EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]


def convert(path):
    raw = path.read_text().replace('\\\n', ' ').splitlines()
    lines = [s.split('#', 1)[0].strip() for s in raw]
    lines = [s for s in lines if s]
    inputs, outputs, nodes = [], [], {}
    idx = 0
    while idx < len(lines):
        words = lines[idx].split()
        idx += 1
        cmd = words[0]
        if cmd == '.model' or cmd == '.end':
            continue
        if cmd == '.inputs':
            inputs.extend(words[1:]); continue
        if cmd == '.outputs':
            outputs.extend(words[1:]); continue
        if cmd == '.gate':
            cell = words[1]
            pins = dict(w.split('=', 1) for w in words[2:])
            assert 'O' in pins, (cell, pins)
            out = pins.pop('O')
            assert out not in nodes
            nodes[out] = ('gate', cell, pins)
            continue
        if cmd == '.names':
            deps, out = words[1:-1], words[-1]
            rows = []
            while idx < len(lines) and not lines[idx].startswith('.'):
                rows.append(lines[idx].split()); idx += 1
            assert out not in nodes
            nodes[out] = ('names', deps, rows)
            continue
        raise ValueError('unsupported BLIF directive: ' + cmd)
    assert inputs == ['x' + str(i) for i in range(10)], inputs
    assert len(outputs) == 1, outputs
    gates = []
    wires = dict(zip(inputs, range(10)))
    visiting = set()
    negations = {}
    false = 1000000
    true = None

    def add(op, pins):
        gates.append({'op': op, 'inputs': pins})
        return 9 + len(gates)

    def inv(a):
        if a in negations:
            return negations[a]
        b = add('not', [a])
        negations[a] = b
        negations[b] = a
        return b

    def const(value):
        nonlocal true
        if not value:
            return false
        if true is None:
            true = add('and', [])
        return true

    def truth(deps, rows):
        arity = len(deps)
        assert arity <= 2, (arity, deps, rows)
        result = 0
        output_values = {r[-1] for r in rows}
        assert len(output_values) <= 1, output_values
        off = output_values == {'0'}
        for assignment in range(1 << arity):
            match = False
            for row in rows:
                if not arity:
                    assert len(row) == 1
                    match = True
                else:
                    assert len(row) == 2 and len(row[0]) == arity
                    match |= all(ch == '-' or int(ch) == (assignment >> j & 1) for j, ch in enumerate(row[0]))
            if match != off:
                result |= 1 << assignment
        return result

    def realize_table(ds, table):
        full = (1 << (1 << len(ds))) - 1
        if table in (0, full):
            return const(table == full)
        if len(ds) == 1:
            return ds[0] if table == 2 else inv(ds[0])
        a, b = ds
        if table == 10: return a
        if table == 12: return b
        if table == 5: return inv(a)
        if table == 3: return inv(b)
        if table == 8: return add('and', [a, b])
        if table == 14: return add('or', [a, b])
        if table == 7: return inv(add('and', [a, b]))
        if table == 1: return inv(add('or', [a, b]))
        terms = []
        for mask in range(4):
            if table >> mask & 1:
                terms.append(add('and', [a if mask & 1 else inv(a), b if mask & 2 else inv(b)]))
        out = terms[0]
        for term in terms[1:]: out = add('or', [out, term])
        return out

    def wire(name):
        if name in wires: return wires[name]
        assert name not in visiting, 'cycle'
        visiting.add(name)
        node = nodes[name]
        if node[0] == 'names':
            out = realize_table([wire(d) for d in node[1]], truth(node[1], node[2]))
        else:
            _, cell, pins = node
            if cell in ('CONST0', 'CONST1'):
                out = const(cell == 'CONST1')
            elif cell == 'BUF':
                out = wire(pins['A'])
            elif cell == 'NOT':
                out = inv(wire(pins['A']))
            elif cell in ('AND2', 'OR2', 'NAND2', 'NOR2'):
                out = add('and' if cell in ('AND2', 'NAND2') else 'or', [wire(pins['A']), wire(pins['B'])])
                if cell in ('NAND2', 'NOR2'): out = inv(out)
            else:
                raise ValueError('unsupported mapped cell: ' + cell)
        visiting.remove(name)
        wires[name] = out
        return out

    output = wire(outputs[0])
    errors = []
    for mask in range(1024):
        values = [bool(mask >> i & 1) for i in range(10)]
        for gate in gates:
            pins = [values[i] if i < len(values) else False for i in gate['inputs']]
            val = all(pins) if gate['op'] == 'and' else any(pins) if gate['op'] == 'or' else not (pins[0] if pins else False)
            values.append(val)
        got = values[output] if output < len(values) else False
        expected = any(mask >> a & 1 and mask >> b & 1 for a, b in EDGES)
        if got != expected: errors.append(mask)
    return {'n': 10, 'gates': gates, 'output': output, 'gate_count': len(gates), 'not_count': sum(g['op'] == 'not' for g in gates), 'errors': errors}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('blif', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    result = convert(args.blif)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['gate_count', 'not_count', 'errors']}))
    if result['errors']: raise SystemExit(1)
