import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser(description='Independent truth-table check of the auxiliary nine-gate two-output circuit.')
parser.add_argument('source', type=Path)
args = parser.parse_args()
data = json.loads(args.source.read_text())
all_bits = (1 << 8192) - 1
columns = [sum(1 << x for x in range(8192) if x >> p & 1) for p in range(13)]
values = columns.copy()
for op, inputs in data['gates']:
    assert op in ('and', 'or') and len(inputs) <= 2
    assert all(0 <= i < len(values) for i in inputs)
    value = all_bits if op == 'and' else 0
    for i in inputs:
        value = value & values[i] if op == 'and' else value | values[i]
    values.append(value)
band = sum(1 << x for x in range(8192) if x.bit_count() in (7, 8))
errors, differences = [], []
for w, out in zip(data['line_ids'], data['outputs']):
    target = 0
    for p in ((w + d) % 13 for d in (0, 1, 3, 9)):
        target |= columns[p]
    assert values[out] & ~target == 0
    errors.append(((values[out] ^ target) & band).bit_count())
    differences.append((values[out] ^ target).bit_count())
    witness = data['nonordinary_witness']
    assert not (values[out] >> witness & 1) and target >> witness & 1
assert len(data['gates']) == 9 and errors == [0, 0] and differences == [32, 32]
print(json.dumps({
    'status': 'INDEPENDENT_PASS', 'method': '8192-bit truth columns',
    'gates': 9, 'global_input_rows': 8192, 'band_rows': band.bit_count(),
    'band_errors': errors, 'global_upper_errors': [0, 0],
    'global_differences': differences, 'nonordinary_witness': witness,
    'scope': 'Refutes only the proposed ten-gate bound for two nonordinary OR outputs; not the thirteen-output posted theorem.'
}, indent=2))
