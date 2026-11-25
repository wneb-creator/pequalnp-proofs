import itertools
import json
import pathlib
import runpy

HERE = pathlib.Path(__file__).resolve().parent
Builder = runpy.run_path(str(HERE/'generate_full_guard_seeds.py'))['Builder']
geometry = json.loads((HERE/'geometry.json').read_text())
neighbors = [{b for a, b in geometry['edges'] if a == p} for p in range(13)]
six = json.loads((HERE/'six-owner-gadgets.json').read_text())[1]
group = [0, 2, 3, 7]
originals = [0, 2, 3, 7, 14, 13, 22, 19, 20, 24, 16, 25, 23, 15]
assert set(originals[4:]) == set.union(*(neighbors[p] for p in group))
local = {v: i for i, v in enumerate(originals)}
edges = [[local[p], local[l]] for p in group for l in sorted(neighbors[p])]
raw = len(originals)
negatives = []
for mask in range(1 << raw):
    if any(mask >> a & 1 and mask >> b & 1 for a, b in edges):
        continue
    if all(any((mask | 1 << v) >> a & 1 and (mask | 1 << v) >> b & 1 for a, b in edges)
           for v in range(raw) if not (mask >> v & 1)):
        negatives.append(mask)
assert len(negatives) == 16
tests = [[(1 << a) | (1 << b), 1] for a, b in edges]+[[mask, 0] for mask in negatives]
builder = Builder(26)
required = [set(six['features'][i-17]['original_lines']) for i in (23, 24, 26)]
for point in range(13):
    if point in group:
        continue
    part = neighbors[point] & set(originals[4:])
    selected = [pair for pair in required if pair <= part]
    assert len(selected) <= 1
    if selected:
        builder.union(selected[0])
    builder.union(part)
line_mask = sum(1 << l for l in originals[4:])
features = []
for mask, wire in builder.unions.items():
    if wire >= 26 and mask & line_mask == mask and mask.bit_count() >= 2:
        features.append(dict(original_lines=[l for l in originals[4:] if mask >> l & 1],
                             raw_indices=[local[l] for l in originals[4:] if mask >> l & 1],
                             outside_wire=wire))
features.sort(key=lambda f: f['outside_wire'])
assert len(features) == 15
terms = [builder.gate(0, p, builder.union(neighbors[p])) for p in range(13) if p not in group]
outside_output = terms[0]
for term in terms[1:]:
    outside_output = builder.gate(1, outside_output, term)
assert len(builder.gates) == 44
extended = []
for mask, label in tests:
    value = mask
    for i, feature in enumerate(features):
        if any(mask >> j & 1 for j in feature['raw_indices']):
            value |= 1 << (raw+i)
    extended.append([value, label])
case = dict(name='context_arc_0_2_3_7', group=group, raw_inputs=raw, input_original=originals,
            inputs=raw+len(features), features=features, edges=edges, raw_tests=tests,
            tests=extended, max_gates=18, outside_gates=builder.gates,
            outside_output=outside_output, outside_cost=44, final_or_cost=1,
            total_if_target_met=63, private_raw_indices=[10, 11, 12, 13],
            kernel_raw_indices=list(range(10)),
            kernel_features=[[5, 8], [4, 7], [6, 9]])
(HERE/'context-four-owner-packet.json').write_text(json.dumps([case]))
source = json.loads((HERE/'feature6-context-27g-best-25.json').read_text())[:17]
mapping = {i: local[v] for i, v in enumerate(six['input_original']) if v in local}
for i, f in enumerate(six['features']):
    for j, g in enumerate(features):
        if set(f['original_lines']) == set(g['original_lines']):
            mapping[17+i] = raw+j
gadget = []
for i, (op, a, b) in enumerate(source):
    gadget.append([op, mapping[a], mapping[b]])
    mapping[30+i] = case['inputs']+i
assert len(gadget) == 17
(HERE/'context-four-owner-seed17.json').write_text(json.dumps(gadget)+'\n')

# This restricted seed is diagnostic only; restoration is not asserted.
kernel_features = [{5, 8}, {4, 7}, {6, 9}]
ren = {i: i if i < 10 else -1 for i in range(raw)}
for i, f in enumerate(features):
    remaining = set(f['raw_indices']) & set(range(10))
    if not remaining:
        ren[raw+i] = -1
    elif len(remaining) == 1:
        ren[raw+i] = next(iter(remaining))
    else:
        ren[raw+i] = 10+kernel_features.index(remaining)
kernel = []
for i, (op, a, b) in enumerate(gadget):
    a, b = ren[a], ren[b]
    if a == b:
        value = a
    elif a == -1 or b == -1:
        value = (b if a == -1 else a) if op else -1
    else:
        value = 13+len(kernel)
        kernel.append([op, a, b])
    ren[case['inputs']+i] = value
assert ren[case['inputs']+len(gadget)-1] == 12+len(kernel)
(HERE/'context-four-owner-kernel13.json').write_text(json.dumps(kernel)+'\n')
print(dict(raw_inputs=raw, features=len(features), outside_gates=len(builder.gates),
           gadget_gates=len(gadget), gadget_ands=sum(op == 0 for op, _, _ in gadget),
           restricted_kernel_gates=len(kernel), restricted_kernel_ands=sum(op == 0 for op, _, _ in kernel)))
