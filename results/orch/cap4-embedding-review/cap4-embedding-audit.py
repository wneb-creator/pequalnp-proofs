import argparse
import hashlib
import itertools
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('truth')
parser.add_argument('local_program')
parser.add_argument('global_program')
parser.add_argument('fixed_samples')
parser.add_argument('output_directory')
args = parser.parse_args()
paths = [Path(getattr(args, name)) for name in ['truth', 'local_program', 'global_program', 'fixed_samples']]
data, local, global_program, samples = [json.loads(p.read_text()) for p in paths]
out = Path(args.output_directory)
out.mkdir(parents=True, exist_ok=True)
vertices = [0, 1, 2, 5, 13, 14, 15, 17, 18, 19, 22, 23, 24, 25]
assert data['vertices'] == vertices and len(set(vertices)) == 14
incidence = lambda p, l: (p - l) % 13 in (0, 1, 3, 9)
line_points = [sum(1 << p for p in range(13) if incidence(p, l)) for l in range(13)]
point_lines = [sum(1 << l for l in range(13) if incidence(p, l)) for p in range(13)]
point_mask = sum(1 << p for p in vertices[:4])
assert max((point_mask & line).bit_count() for line in line_points) == 2
assert vertices[4:] == [13 + l for l in range(13) if point_mask & line_points[l]]
positive = [(1 << ((l + d) % 13)) | (1 << (13 + l)) for l in range(13) for d in (0, 1, 3, 9)]
assert positive == samples['positive_samples'] and len(set(positive)) == 52
generic = []
for points in range(1 << 13):
    lines = sum(1 << l for l in range(13) if not points & line_points[l])
    completed_points = sum(1 << p for p in range(13) if not lines & point_lines[p])
    if completed_points != points:
        continue
    if any(points & ~line == 0 for line in line_points):
        continue
    if any(lines & ~star == 0 for star in point_lines):
        continue
    generic.append(points | (lines << 13))
assert len(generic) == 468 and set(generic) == set(samples['negative_samples'])
project = lambda mask: sum(((mask >> v) & 1) << i for i, v in enumerate(vertices))
local_edges = {project(mask) for mask in positive if all(v in vertices for v in range(26) if mask >> v & 1)}
assert len(local_edges) == 16 and local_edges == set(data['positive_edges'])
projections = {project(mask) for mask in generic}
maxima = {q for q in projections if not any(q != r and q & ~r == 0 for r in projections)}
assert len(projections) == 222 and len(maxima) == 83
assert maxima == set(data['maximal_negative_masks'])
assert all(any(q & ~r == 0 for r in maxima) for q in projections)
assert [project(mask) for mask in samples['negative_samples']] == data['original_projected_negative_masks']

def validate(program, n, k):
    assert type(program['input_count']) is int and program['input_count'] == n
    assert type(program['or_count']) is int and program['or_count'] == k
    assert len(program['operand_wire_lists']) == k
    for g, pair in enumerate(program['operand_wire_lists']):
        assert len(pair) == 2
        assert all(type(ref) is int and 0 <= ref < n + g for branch in pair for ref in branch)
    assert all(type(ref) is int and 0 <= ref < n + k for ref in program['output_wire_list'])

def evaluate(program, sample):
    values = [bool(sample >> i & 1) for i in range(program['input_count'])]
    for left, right in program['operand_wire_lists']:
        values.append(all(values[i] for i in left) or all(values[i] for i in right))
    return all(values[i] for i in program['output_wire_list'])

validate(local, 14, 15)
validate(global_program, 26, 51)
for mask in range(1 << 14):
    assert evaluate(local, mask) == any(mask & edge == edge for edge in local_edges)
lift = lambda ref: vertices[ref] if ref < 14 else 26 + ref - 14
expected = [[[lift(ref) for ref in branch] for branch in pair] for pair in local['operand_wire_lists']]
expected_output = [lift(ref) for ref in local['output_wire_list']]
remaining = [(p, 13 + l) for p in range(13) for l in range(13)
             if incidence(p, l) and not (p in vertices and 13 + l in vertices)]
assert len(remaining) == 36
for p, l in remaining:
    expected.append([expected_output, [p, l]])
    expected_output = [26 + len(expected) - 1]
assert global_program['operand_wire_lists'] == expected
assert global_program['output_wire_list'] == expected_output

def minimal(terms):
    return {term for term in terms if not any(other != term and other & term == other for other in terms)}

def conjunction_terms(values, refs):
    result = {0}
    for ref in refs:
        result = minimal({a | b for a in result for b in values[ref]})
    return result

term_values = [{1 << i} for i in range(26)]
for left, right in global_program['operand_wire_lists']:
    term_values.append(minimal(conjunction_terms(term_values, left) | conjunction_terms(term_values, right)))
terms = conjunction_terms(term_values, global_program['output_wire_list'])
assert terms == set(positive)
checks = [(mask, True) for mask in positive] + [(mask, False) for mask in generic]
checks += [(1 << i, False) for i in range(26)] + [(0, False)]
assert len(checks) == 547
assert all(evaluate(global_program, mask) == wanted for mask, wanted in checks)

ordered_samples = positive + samples['negative_samples']
truth_mask = (1 << 520) - 1
inputs = [sum(1 << r for r, mask in enumerate(ordered_samples) if mask >> i & 1) for i in range(26)]
assert inputs == samples['input_masks']
mask_values = inputs[:]
certificates = []
def conjunction_masks(refs):
    value = truth_mask
    for ref in refs:
        value &= mask_values[ref]
    return value
for left, right in global_program['operand_wire_lists']:
    value = conjunction_masks(left) | conjunction_masks(right)
    certificates.append(value)
    mask_values.append(value)
result = conjunction_masks(global_program['output_wire_list'])
assert result == (1 << 52) - 1
mask_report = {
    'sample_count': 520, 'positive_count': 52, 'negative_count': 468,
    'input_masks': inputs, 'or_masks': certificates, 'output_mask': result,
    'positive_samples': positive, 'negative_samples': samples['negative_samples'],
    'scope': '51OR full baseline control only; not a counterexample and not Lean checked',
}
(out / 'cap4-direct15-global51-masks.json').write_text(json.dumps(mask_report, indent=2) + '\n')
report = {
    'verdict': 'PASS (independent Python and symbolic-DNF audit; no Lean or solver)',
    'inputs': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
    'vertices': vertices, 'local_edges': 16, 'global_remaining_edges': 36,
    'independently_enumerated_generic_rows': len(generic), 'distinct_projections': len(projections),
    'maximal_projections': len(maxima), 'local_full_assignment_checks': 1 << 14,
    'global_control_or_count': 51, 'global_boolean_sample_checks': len(checks),
    'global_symbolic_minimal_terms_equal_exact52_incidence_edges': True,
    'compiler_sample_order_and_all13520_input_bits_match_checked_data': True,
    'conditional14OR_local_implies50OR_global': True,
    'actual14OR_local_witness_exists': False,
}
(out / 'cap4-embedding-review.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
