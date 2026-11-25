import json
from pathlib import Path

base = Path(__file__).resolve().parent
original = json.loads((base/'pg3-marginal48-pair-only.json').read_text())
data = json.loads((base/'theta4-control-global51-masks.json').read_text())
truth, positives = (1 << 520)-1, (1 << 52)-1
old_values = list(data['input_masks'])
values = list(old_values)
operations, operand_signatures, masks = [], [], []

def conjunction(wires, refs):
    answer = truth
    for ref in refs:
        answer &= wires[ref]
    return answer

for step, operands in enumerate(original['operand_wire_lists']):
    closed, signatures, terms = [], [], []
    for refs in operands:
        signature = conjunction(values, refs) & positives
        closure = [j for j, value in enumerate(values) if value & signature == signature]
        assert set(refs).issubset(closure)
        term = conjunction(values, closure)
        assert term & positives == signature
        closed.append(closure)
        signatures.append(signature)
        terms.append(term)
    value = terms[0] | terms[1]
    old_value = conjunction(old_values, operands[0]) | conjunction(old_values, operands[1])
    assert value & positives == old_value & positives
    assert value & ~old_value == 0
    old_values.append(old_value)
    values.append(value)
    operations.append(closed)
    operand_signatures.append(signatures)
    masks.append(value)

output_signature = conjunction(values, original['output_wire_list']) & positives
output_refs = [j for j, value in enumerate(values) if value & output_signature == output_signature]
output = conjunction(values, output_refs)
old_output = conjunction(old_values, original['output_wire_list'])
assert output & positives == positives
assert output & ~old_output == 0
groups = {
    'A_point_x': {'or_indices': list(range(0, 6)), 'output_signal_refs': [27, 29, 31]},
    'B_point_y': {'or_indices': list(range(6, 12)), 'output_signal_refs': [33, 35, 37]},
    'S_line_slope': {'or_indices': list(range(12, 18)), 'output_signal_refs': [39, 41, 43]},
    'T_line_intercept': {'or_indices': list(range(18, 24)), 'output_signal_refs': [45, 47, 49]},
    'W_product_classes': {'or_indices': [24, 25, 26], 'output_signal_refs': [50, 51, 52]},
    'E_coordinate_difference': {'or_indices': list(range(27, 33)), 'output_signal_refs': [54, 56, 58]},
    'affine_incidence': {'or_indices': [33, 34], 'output_signal_refs': [60]},
    'affine_vertical': {'or_indices': [35, 36], 'output_signal_refs': [62]},
    'infinity_slope': {'or_indices': [37, 38], 'output_signal_refs': [64]},
    'all_vertical_lines': {'or_indices': [39, 40], 'output_signal_refs': [66]},
    'all_infinity_points': {'or_indices': [41, 42, 43], 'output_signal_refs': [69]},
    'final_five_block_union': {'or_indices': [44, 45, 46, 47], 'output_signal_refs': [73]},
}
result = {'input_count': 26, 'or_count': 48, 'operand_wire_lists': operations,
          'operand_signatures': operand_signatures, 'output_wire_list': output_refs,
          'groups': groups, 'checked_positive_samples': 52, 'checked_negative_samples': 468,
          'negative_false_positives': (output >> 52).bit_count(),
          'scope': 'INVALID repair seed; full positive closure normalization; not a refutation'}
(base/'pg3-marginal48-canonical-invalid.json').write_text(json.dumps(result, indent=2)+'\n')
certificate = {'sample_count': 520, 'positive_count': 52, 'negative_count': 468,
               'input_masks': data['input_masks'], 'or_masks': masks, 'output_mask': output,
               'positive_samples': data['positive_samples'], 'negative_samples': data['negative_samples'],
               'scope': 'INVALID repair seed masks; output has forbidden negative bits'}
(base/'pg3-marginal48-canonical-invalid-masks.json').write_text(json.dumps(certificate, indent=2)+'\n')
report = {'or_count': 48, 'old_bad_generic_rows': (old_output >> 52).bit_count(),
          'canonical_bad_generic_rows': (output >> 52).bit_count(),
          'all52_positive_flags_preserved': True,
          'every_wire_negative_values_only_decreased': True,
          'operand_references_before': sum(map(len, sum(original['operand_wire_lists'], []))),
          'operand_references_after': sum(map(len, sum(operations, []))),
          'is_counterexample': (output >> 52) == 0}
(base/'pg3-marginal48-canonical-report.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
