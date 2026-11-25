from pathlib import Path
import json
import sys

ALL = (1 << 1024) - 1
EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
         (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
INPUTS = [sum(1 << r for r in range(1024) if (r >> i) & 1) for i in range(10)]
TARGET = 0
for a, b in EDGES:
    TARGET |= INPUTS[a] & INPUTS[b]

def operation(d, a, b):
    return [a & b, a | b, a & (ALL ^ b), (ALL ^ a) & b][d]

def normalize(lines):
    ids = {i + 1: i for i in range(10)}
    values = INPUTS.copy()
    gates = []
    for line in lines:
        if not line.startswith('gate '):
            continue
        _, d, a, b, z = line.split()
        d, a, b, z = map(int, (d, a, b, z))
        assert d in range(4) and a in ids and b in ids
        aa, bb = ids[a], ids[b]
        gates.append((d, aa, bb))
        values.append(operation(d, values[aa], values[bb]))
        if z in ids:
            assert values[ids[z]] == values[-1]
        ids[z] = len(values) - 1
    assert gates and values[-1] == TARGET
    return gates, values

def phases(gates, complemented):
    n = 10 + len(gates)
    parent = list(range(n + 1))
    parity = [0] * (n + 1)
    def find(a):
        if parent[a] != a:
            p, q = find(parent[a])
            parity[a] ^= q
            parent[a] = p
        return parent[a], parity[a]
    def union(a, b, difference):
        pa, qa = find(a)
        pb, qb = find(b)
        if pa == pb:
            return qa ^ qb == difference
        parent[pa] = pb
        parity[pa] = qa ^ qb ^ difference
        return True
    for i in range(10):
        if not union(i, n, 0):
            return None
    if complemented != n - 1 and not union(n - 1, n, 0):
        return None
    for out, (d, a, b) in enumerate(gates, 10):
        for operand, inverted in [(a, int(d == 3)), (b, int(d == 2))]:
            if operand != complemented and not union(operand, out, inverted):
                return None
    anchor, offset = find(n)
    answer = []
    for i in range(n):
        component, bit = find(i)
        answer.append(bit ^ (offset if component == anchor else 0))
    return answer

def realize(gates, phase, complemented):
    values = INPUTS.copy()
    circuit = []
    refs = list(range(10))
    complement_ref = None
    def add(op, args, value):
        index = len(values)
        circuit.append({'op': op, 'inputs': args})
        values.append(value)
        return index
    if complemented is not None and complemented < 10:
        complement_ref = add('not', [complemented], ALL ^ values[complemented])
    for out, (d, a, b) in enumerate(gates, 10):
        args = []
        for operand, inverted in [(a, int(d == 3)), (b, int(d == 2))]:
            wanted = phase[out] ^ inverted
            if wanted == phase[operand]:
                args.append(refs[operand])
            else:
                assert operand == complemented and complement_ref is not None
                args.append(complement_ref)
        is_or = int(d == 1) ^ phase[out]
        result = (values[args[0]] | values[args[1]]) if is_or else (values[args[0]] & values[args[1]])
        refs.append(add('or' if is_or else 'and', args, result))
        if out == complemented:
            complement_ref = add('not', [refs[out]], ALL ^ result)
    output = refs[-1] if phase[-1] == 0 else complement_ref
    assert output is not None and values[output] == TARGET
    return {'gates': circuit, 'output': output, 'total_gates': len(circuit),
            'not_gates': sum(g['op'] == 'not' for g in circuit),
            'all_1024_rows_match': True}

def examine(gates):
    for complemented in [None] + list(range(10 + len(gates))):
        p = phases(gates, complemented)
        if p is not None:
            result = realize(gates, p, complemented)
            result.update({'normalized_binary_gates': len(gates),
                           'complemented_wire': complemented, 'phases': p})
            return result
    return {'normalized_binary_gates': len(gates), 'all_1024_rows_match': True,
            'one_not_phase_realization': False,
            'scope': 'This excludes only phase realizations of this gate DAG, not all circuits.'}

if len(sys.argv) == 2 and sys.argv[1] == '--selftest':
    gates = [(1,1,4),(1,10,5),(0,0,11),(1,2,6),(0,1,13),(1,2,4),
             (1,15,8),(0,3,16),(1,2,5),(1,18,9),(0,7,19),(1,6,5),
             (0,8,21),(1,4,6),(0,9,23),(1,12,14),(1,25,17),(1,26,20),
             (1,27,22),(1,28,24)]
    answer = examine(gates)
    assert answer['total_gates'] == 20 and answer['not_gates'] == 0
    transformed = []
    refs = list(range(10))
    for original, (d, a, b) in enumerate(gates, 10):
        aa, bb = refs[a], refs[b]
        if original == 12:
            assert d == 0
            temporary = 10 + len(transformed)
            transformed.append((2, aa, bb))
            transformed.append((2, aa, temporary))
        else:
            transformed.append((d, aa, bb))
        refs.append(9 + len(transformed))
    with_not = examine(transformed)
    assert with_not['total_gates'] == 22 and with_not['not_gates'] == 1
    print(json.dumps({'positive_controls': 'passed', 'monotone': answer,
                      'one_not_phase_control': with_not}, indent=2))
else:
    path = Path(sys.argv[1])
    lines = path.read_text().splitlines()
    if 'finished found=1' not in lines:
        print(json.dumps({'witness_present': False,
                          'scope': 'No candidate is present in this bounded-run log.'}))
    else:
        gates, _ = normalize(lines)
        print(json.dumps(examine(gates), indent=2))
