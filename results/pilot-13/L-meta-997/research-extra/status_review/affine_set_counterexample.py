import hashlib
import json
from pathlib import Path


def mul(a, b):
    answer = 0
    while b:
        if b & 1:
            answer ^= a
        a <<= 1
        if a & 16:
            a ^= 19
        b >>= 1
    return answer


assert all(len({mul(a,b) for b in range(16)}) == 16 for a in range(1,16))
n = 256
values = [1 << p for p in range(n)]
gates = []


def gate(op, a, b):
    gates.append((op,a,b))
    values.append(values[a] & values[b] if op == 'and' else values[a] | values[b])
    return len(values)-1


def union(wires):
    result = wires[0]
    for wire in wires[1:]:
        result = gate('or',result,wire)
    return result


def xor_dual(a, b):
    zero = gate('or',gate('and',a[0],b[0]),gate('and',a[1],b[1]))
    one = gate('or',gate('and',a[0],b[1]),gate('and',a[1],b[0]))
    return (zero,one)


def equalities(bits):
    prefixes = {0:bits[0][0],1:bits[0][1]}
    for j in range(1,4):
        prefixes = {p | (v << j):gate('and',wire,bits[j][v])
                    for p,wire in prefixes.items() for v in range(2)}
    return prefixes


coordinates = [(union([p for p in range(256) if not (p >> j) & 1]),
                union([p for p in range(256) if (p >> j) & 1])) for j in range(8)]
coordinate_gates = len(gates)
outputs = []
xor_count = 0
for slope in range(16):
    bits = []
    for j in range(4):
        bit = coordinates[4+j]
        for k in range(4):
            if (mul(slope,1 << k) >> j) & 1:
                bit = xor_dual(bit,coordinates[k])
                xor_count += 1
        bits.append(bit)
    eq = equalities(bits)
    for intercept,wire in eq.items():
        expected = sum(1 << (x + 16*y) for x in range(16) for y in range(16)
                       if y == (mul(slope,x) ^ intercept))
        assert values[wire] == expected
        outputs.append(wire)
vertical = equalities(coordinates[:4])
for x,wire in vertical.items():
    assert values[wire] == sum(1 << (x + 16*y) for y in range(16))
    outputs.append(wire)
sets = [values[w] for w in outputs]
assert len(sets) == 272 and len(set(sets)) == 272
assert all(s.bit_count() == 16 for s in sets)
assert all((s&t).bit_count() <= 1 for i,s in enumerate(sets) for t in sets[i+1:])
lower_claim = sum(s.bit_count()-1 for s in sets)
assert len(gates) < lower_claim
result = {
    'scope':'Counterexample only to abstract singleton-support/set-lattice lower bound; not to L-meta-997.',
    'inputs':n,'outputs':len(outputs),'set_cardinality':16,
    'pairwise_intersection_at_most_one':True,
    'coordinate_union_gates':coordinate_gates,'dual_xor_operations':xor_count,
    'dual_xor_gates':xor_count*6,'equality_and_gates':17*28,
    'total_and_or_gates':len(gates),'sum_card_minus_one':lower_claim,
    'saved_gates_against_false_bound':lower_claim-len(gates),
    'all_output_masks_checked':True,
    'instruction_sha256':hashlib.sha256(json.dumps(gates,separators=(',',':')).encode()).hexdigest(),
    'warning':'AND of singleton-support sets models intersections; actual Boolean gate functions need not be ORs of those sets.'}
out=Path('/tmp/oec/pequalnp-pilot-13/status_review/affine_set_counterexample.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
