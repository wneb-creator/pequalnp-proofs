import hashlib
import json
from pathlib import Path


root = Path(__file__).resolve().parent
data = json.loads((root.parent / 'plane2056-sat' / 'plane2056-data.json').read_text())
edges, rows = data['edges'], data['rows']
n = 26
edge_masks = {(1 << a) | (1 << b) for a, b in edges}
positive = (1 << len(edges)) - 1
negative = ((1 << len(rows)) - 1) ^ positive
inputs = [sum(((r >> i) & 1) << j for j, r in enumerate(rows)) for i in range(n)]
neighbors = [[] for _ in range(n)]
for point, line in edges:
    neighbors[point].append(line)
    neighbors[line].append(point)


def minimal(monomials):
    result = []
    for term in sorted(set(monomials), key=lambda x: (x.bit_count(), x)):
        if not any(previous & term == previous for previous in result):
            result.append(term)
    return result


seeds = []
for c in range(13, 26):
    b1, b2, a1, a2 = sorted(neighbors[c])
    for a_count in (1, 2):
        a_set = [a1, a2][:a_count]
        for first_count in (1, 2):
            for second_count in (1, 2):
                first_leaves = sorted(line for line in neighbors[b1] if line != c)
                second_leaves = sorted(line for line in neighbors[b2] if line != c)
                first_block = first_leaves[:first_count]
                second_block = second_leaves[:second_count]
                t1 = first_leaves[first_count:]
                t2 = second_leaves[second_count:]
                assert t1 and t2
                gates = []

                def gate(op, left, right):
                    gates.append([op, left, right])
                    return n + len(gates) - 1

                def fold(wires):
                    assert wires
                    result = wires[0]
                    for wire in wires[1:]:
                        result = gate(1, result, wire)
                    return result

                d1_left = fold([b1] + a_set)
                d1_right = fold([c] + first_block)
                dirty1 = gate(0, d1_left, d1_right)
                d2_left = gate(1, dirty1, b2)
                d2_right = fold([c] + second_block)
                dirty2 = gate(0, d2_left, d2_right)
                context1 = gate(1, dirty1, fold(t1))
                star1 = gate(0, b1, context1)
                context2 = gate(1, dirty2, fold(t2))
                star2 = gate(0, b2, context2)
                line_star = gate(0, c, dirty2)
                region = fold([star1, star2, line_star])
                assert len(gates) == a_count + 14
                terms = [region]
                for point in range(13):
                    if point in (b1, b2):
                        continue
                    leaves = [line for line in neighbors[point]
                              if not (point in a_set and line == c)]
                    terms.append(gate(0, point, fold(leaves)))
                output = fold(terms)
                assert len(gates) == 69
                values = inputs.copy()
                zero = inputs.copy()
                one = inputs.copy()
                dnf = [[1 << i] for i in range(n)]
                violations = 0
                dominated = []
                dirty_ands = []
                for j, (op, left, right) in enumerate(gates):
                    assert 0 <= left < len(values) and 0 <= right < len(values)
                    x, y = values[left], values[right]
                    value = x | y if op else x & y
                    clean_x, clean_y = not (x & negative), not (y & negative)
                    violations += ((not op and (clean_x or clean_y))
                                   or (op and clean_x != clean_y))
                    for earlier, previous in enumerate(values):
                        if not ((value & positive) & ~previous) and not ((previous & negative) & ~value):
                            dominated.append([n + j, earlier])
                    values.append(value)
                    one.append((one[left] | one[right]) if op else (zero[left] & zero[right]))
                    zero.append((zero[left] | zero[right]) if op else 0)
                    dnf.append(minimal(dnf[left] + dnf[right] if op else
                                       [a | b for a in dnf[left] for b in dnf[right]]))
                    if not op and value & negative:
                        dirty_ands.append(n + j)
                assert values[output] == positive and set(dnf[output]) == edge_masks
                assert dirty_ands == [dirty1, dirty2]
                assert violations == 0 and not dominated
                false_monomials = []
                frontiers = []
                for dirty in [dirty1, dirty2]:
                    false_terms = [m for m in dnf[dirty] if not any(e & m == e for e in edge_masks)]
                    assert false_terms
                    false_monomials.append(false_terms)
                    assert sum(left == dirty for _, left, _ in gates) + sum(right == dirty for _, _, right in gates) == 2
                    reachable = {dirty}
                    frontier = []
                    for j, (op, left, right) in enumerate(gates):
                        if left in reachable or right in reachable:
                            if op:
                                reachable.add(n + j)
                            else:
                                frontier.append(n + j)
                    frontiers.append(frontier)
                assert frontiers == [[dirty2, star1], [star2, line_star]]
                assert {m.bit_count() for m in false_monomials[0]} == {2}
                assert {m.bit_count() for m in false_monomials[1]} == {3}
                seeds.append({
                    'line_center': c, 'point_centers': [b1, b2], 'line_star_leaves': a_set,
                    'private_blocks': [first_block, second_block], 'T': [t1, t2],
                    'gates': gates, 'output': output, 'size': len(gates),
                    'dirty_and_wires': dirty_ands, 'dirty_next_and_frontiers': frontiers,
                    'dirty_direct_uses': [2, 2], 'dirty_false_dnf_monomials': false_monomials,
                    'normalization_violations': violations, 'dominated_gates': len(dominated),
                    'accepted_without_read1': (positive & ~one[output]).bit_count(),
                    'symbolic_dnf_exact_edges': len(edge_masks),
                })
assert len(seeds) == 104
destination = root / 'full-nested-dirty-seeds.json'
destination.write_text(json.dumps(seeds, separators=(',', ':')) + '\n')
print(json.dumps({
    'seeds': len(seeds), 'sizes': sorted({s['size'] for s in seeds}),
    'dirty_AND_count': 2, 'false_DNF_degrees': [2, 3],
    'nonread1': sorted({s['accepted_without_read1'] for s in seeds}),
    'sha256': hashlib.sha256(destination.read_bytes()).hexdigest(),
}), flush=True)
