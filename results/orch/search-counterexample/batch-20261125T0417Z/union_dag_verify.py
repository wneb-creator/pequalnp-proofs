import argparse
import json
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('network')
args = ap.parse_args()
base = Path('/tmp/oec/pequalnp-pilot-62')
data = json.loads((base / 'multi-output-line-neighborhoods.json').read_text())
net = json.loads(Path(args.network).read_text())
assert net['input_count'] == 13
wires = [1 << i for i in range(13)]
for a, b in net['ors']:
    assert 0 <= a < len(wires) and 0 <= b < len(wires)
    wires.append(wires[a] | wires[b])
assert wires[13:] == net['gate_masks']
assert len(net['ors']) == net['or_count']
outputs = [[u for u in wires if u & t['positive_mask'] == t['positive_mask']]
           for t in data['targets']]
def evaluate(output, sample):
    return all(u & sample != 0 for u in output)
violations = []
for p, (target, output) in enumerate(zip(data['targets'], outputs)):
    required = target['positive_mask']
    for i in range(13):
        if required >> i & 1:
            assert evaluate(output, 1 << i)
    for row in target['negative_rows']:
        sample = data['negative_samples'][row]
        if evaluate(output, sample): violations.append([p, sample])
max_requirements = []
for p, target in enumerate(data['targets']):
    rows = sorted({data['negative_samples'][i] for i in target['negative_rows']})
    max_requirements.extend((p, q) for q in rows if not any(q != r and q & r == q for r in rows))
def cover_cost(p, q):
    t = data['targets'][p]['positive_mask']
    available = {w & t for w in wires if not w & q}
    reached = {0}
    for count in range(5):
        if t in reached: return count
        reached |= {u | v for u in reached for v in available}
    raise AssertionError('singleton cover missing')
deficit = sum(cover_cost(p,q)-1 for p,q in max_requirements)
uncovered = sum(evaluate(outputs[p],q) for p,q in max_requirements)
assert deficit == net['cover_deficit']
assert uncovered == net['uncovered_requirements']
assert (not violations) == (deficit == 0)
cap_violations = 0
caps = [q for q in range(8192) if not any(q & t == t for t in data['allowed_concurrent_triples'])]
for target, output in zip(data['targets'], outputs):
    cap_violations += sum(evaluate(output,q) != bool(q & target['positive_mask']) for q in caps)
print(json.dumps({'or_count':len(net['ors']), 'original_negative_violations':len(violations),
                  'maximal_requirements':len(max_requirements), 'cover_deficit':deficit,
                  'uncovered_requirements':uncovered, 'caps_checked':len(caps),
                  'cap_violations':cap_violations, 'valid_separator':not violations}))
if not violations: assert cap_violations == 0
