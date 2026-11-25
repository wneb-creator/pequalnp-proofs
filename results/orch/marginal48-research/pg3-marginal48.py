import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def norm(v):
    v = tuple(x % 3 for x in v)
    a = next(x for x in v if x)
    return tuple(x * pow(a, -1, 3) % 3 for x in v)

orbit = []
v = (1, 0, 0)
for _ in range(13):
    orbit.append(norm(v))
    v = (v[2], (v[0] + v[2]) % 3, v[1])
assert len(set(orbit)) == 13 and norm(v) == orbit[0]
D = {i for i, p in enumerate(orbit) if p[2] == 0}
target = {0, 1, 3, 9}
a, b = next((a, b) for a in range(1, 13) for b in range(13)
            if {(a*d+b) % 13 for d in target} == D)
point_vectors = [orbit[(a*i+b) % 13] for i in range(13)]
point_index = {p: i for i, p in enumerate(point_vectors)}
plane = sorted({norm(v) for v in itertools.product(range(3), repeat=3) if any(v)})
dot = lambda p, l: sum(x*y for x, y in zip(p, l)) % 3
line_vectors = [next(l for l in plane if {p for p in range(13) if dot(point_vectors[p], l) == 0}
                     == {(i+d) % 13 for d in target}) for i in range(13)]
line_index = {l: i for i, l in enumerate(line_vectors)}
assert len(line_index) == 13

P = lambda x, y: point_index[norm((x, y, 1))]
Y = lambda s, t: 13 + line_index[norm((-s, 1, -t))]
Q = lambda s: point_index[norm((1, s, 0))]
Qv = point_index[norm((0, 1, 0))]
V = lambda x: 13 + line_index[norm((1, 0, -x))]
Z = 13 + line_index[norm((0, 0, 1))]
gates = []

def gate(op, x, y):
    gates.append((op, x, y))
    return 25 + len(gates)

def join(xs):
    xs = list(xs)
    r = xs[0]
    for x in xs[1:]:
        r = gate('or', r, x)
    return r

def meet(x, y):
    return gate('and', x, y)

A = [join(P(x, y) for y in range(3)) for x in range(3)]
B = [join(P(x, y) for x in range(3)) for y in range(3)]
S = [join(Y(s, t) for t in range(3)) for s in range(3)]
T = [join(Y(s, t) for s in range(3)) for t in range(3)]
W = [gate('or', A[0], S[0]),
     join([meet(A[1], S[1]), meet(A[2], S[2])]),
     join([meet(A[1], S[2]), meet(A[2], S[1])])]
E = [join(meet(B[(r+t) % 3], T[t]) for t in range(3)) for r in range(3)]
affine = join(meet(W[r], E[r]) for r in range(3))
vertical = join(meet(A[x], V(x)) for x in range(3))
slopes = join(meet(Q(s), S[s]) for s in range(3))
vertical_infinity = meet(Qv, join(V(x) for x in range(3)))
line_infinity = meet(Z, join([Qv] + [Q(s) for s in range(3)]))
output = join([affine, vertical, slopes, vertical_infinity, line_infinity])
assert sum(op == 'or' for op, _, _ in gates) == 48

samples = [sum(1 << i for i in subset) for k in range(4)
           for subset in itertools.combinations(range(26), k)]
export = json.loads((ROOT/'theta4-control-global51-masks.json').read_text())
negatives = export['negative_samples']
assert len(negatives) == 468 and all(type(x) is int for x in negatives)
all_samples = samples + negatives
values = [sum(1 << r for r, mask in enumerate(all_samples) if mask >> i & 1) for i in range(26)]
for op, x, y in gates:
    values.append(values[x] | values[y] if op == 'or' else values[x] & values[y])
out = values[output]
edge = lambda p, l: (p-l) % 13 in target
has_edge = lambda mask: any(mask >> p & 1 and mask >> (13+l) & 1 and edge(p, l)
                           for p in range(13) for l in range(13))
false_positives = []
for r, mask in enumerate(samples):
    result = bool(out >> r & 1)
    wanted = has_edge(mask)
    if mask.bit_count() <= 2:
        assert result == wanted
    if result and not wanted:
        false_positives.append(mask)
counts = {str(k): sum((mask & ((1 << 13)-1)).bit_count() == k for mask in false_positives)
          for k in range(4)}
all_mixed_nonedges = [mask for mask in samples if mask.bit_count() == 3 and not has_edge(mask)
                     and (mask & ((1 << 13)-1)).bit_count() in (1, 2)]
assert len(all_mixed_nonedges) == 936
assert all(any(mask & row == mask for row in negatives) for mask in all_mixed_nonedges)
bad_rows = [r for r in range(468) if out >> (len(samples)+r) & 1]
sample_indices = {mask: i for i, mask in enumerate(samples)}
flag_samples = export['positive_samples']
flag_indices = [sample_indices[mask] for mask in flag_samples]
wire_signatures = [sum(1 << a for a, i in enumerate(flag_indices) if value >> i & 1)
                   for value in values]

def extension_cover_obstruction(sample_index):
    supports = set(signature for signature, value in zip(wire_signatures, values)
                   if signature and not (value >> sample_index & 1))
    maximal = sorted(s for s in supports if not any(s != t and s & t == s for t in supports))
    maxima = {}
    for k in range(1, len(maximal) + 1):
        maxima[str(k)] = max((__import__('functools').reduce(int.__or__, combo, 0).bit_count()
                              for combo in itertools.combinations(maximal, k)), default=0)
        if maxima[str(k)] == 52:
            break
    assert maxima['3'] < 52
    cover = next(combo for combo in itertools.combinations(maximal, k)
                 if __import__('functools').reduce(int.__or__, combo, 0) == (1 << 52)-1)
    assert all(any(s & t == s for t in maximal) for s in supports)
    return {'maximal_false_wire_supports': len(maximal),
            'input_mask': all_samples[sample_index],
            'maximal_support_masks': maximal,
            'minimum_cover_witness': list(cover),
            'maximum_flags_covered_by_k_false_wires': maxima,
            'minimum_false_wire_cover': k,
            'additional_OR_lower_bound': k - 1}

triple_obstruction = extension_cover_obstruction(sample_indices[false_positives[0]])
row_obstruction = extension_cover_obstruction(len(samples) + bad_rows[0])

canonical_refs = [[i] for i in range(26)]
operations = []
for op, x, y in gates:
    if op == 'and':
        canonical_refs.append(sorted(set(canonical_refs[x] + canonical_refs[y])))
    else:
        operations.append([canonical_refs[x], canonical_refs[y]])
        canonical_refs.append([26 + len(operations)-1])
canonical = {'input_count': 26, 'or_count': 48, 'operand_wire_lists': operations,
             'output_wire_list': canonical_refs[output],
             'scope': 'Correct on weights0,1,2 only; not a counterexample to the held gap'}
(ROOT/'pg3-marginal48-pair-only.json').write_text(json.dumps(canonical, indent=2)+'\n')
report = {'or_count': 48, 'and_count': sum(op == 'and' for op, _, _ in gates),
          'all_low_samples': len(samples), 'pair_function_correct': True,
          'false_positive_triples_by_point_count': counts,
          'false_positive_triple_examples': false_positives[:8],
          'mixed_nonedge_triples': len(all_mixed_nonedges),
          'all_mixed_nonedge_triples_covered_by_generic_rows': True,
          'generic_false_positives': len(bad_rows), 'generic_false_positive_indices': bad_rows,
          'first_bad_triple_extension_obstruction': triple_obstruction,
          'first_bad_row_extension_obstruction': row_obstruction,
          'affine_point_labels': [[P(x, y) for y in range(3)] for x in range(3)],
          'affine_line_labels': [[Y(s, t)-13 for t in range(3)] for s in range(3)],
          'infinity_point_labels': [Q(s) for s in range(3)] + [Qv],
          'vertical_line_labels': [V(x)-13 for x in range(3)], 'infinity_line_label': Z-13,
          'scope': 'Python finite check plus explicit algebra; no Lean theorem; not a refutation'}
(ROOT/'pg3-marginal48-report.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({k: v for k, v in report.items() if not k.endswith('_indices')}, indent=2))
