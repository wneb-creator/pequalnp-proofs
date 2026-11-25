import json
import pathlib
import runpy

HERE = pathlib.Path(__file__).resolve().parent
Builder = runpy.run_path(str(HERE/'generate_full_guard_seeds.py'))['Builder']
base = json.loads((HERE/'six-owner-gadgets.json').read_text())[0]
orbits = json.loads((HERE/'six-prefix-orbits.json').read_text())['all_prefix_orbits']
geometry = json.loads((HERE/'geometry.json').read_text())
neighbors = [{b for a, b in geometry['edges'] if a == p} for p in range(13)]
originals = base['input_original']
local = {original: i for i, original in enumerate(originals)}
cases = []
for index, orbit in enumerate(orbits):
    supports = [set(i for i in range(17) if mask >> i & 1)
                for mask in orbit['representative_feature_masks']]
    builder = Builder(26)
    for point in range(13):
        if point in base['group']:
            continue
        lines = neighbors[point] & set(originals[6:])
        raw_lines = {local[line] for line in lines}
        if len(lines) == 3:
            pairs = [s for s in supports if len(s) == 2 and s < raw_lines]
            assert len(pairs) == 1
            builder.union({originals[i] for i in pairs[0]})
        builder.union(lines)
    features = []
    line_mask = sum(1 << line for line in originals[6:])
    for mask, wire in builder.unions.items():
        if wire >= 26 and mask & line_mask == mask and mask.bit_count() >= 2:
            lines = [line for line in originals[6:] if mask >> line & 1]
            features.append(dict(original_lines=lines, raw_indices=[local[line] for line in lines],
                                 outside_wire=wire))
    features.sort(key=lambda f: f['outside_wire'])
    assert len(features) == 13
    assert sorted(sum(1 << i for i in f['raw_indices']) for f in features) == orbit['representative_feature_masks']
    terms = [builder.gate(0, p, builder.union(neighbors[p])) for p in range(13) if p not in base['group']]
    output = terms[0]
    for term in terms[1:]:
        output = builder.gate(1, output, term)
    assert len(builder.gates) == 34
    tests = []
    for mask, label in base['raw_tests']:
        value = mask
        for i, feature in enumerate(features):
            if any(mask >> j & 1 for j in feature['raw_indices']):
                value |= 1 << (17+i)
        tests.append([value, label])
    cases.append(dict(name=f'core6_all_orbit_{index:02d}', group=base['group'], raw_inputs=17,
                      input_original=originals, inputs=30, features=features, edges=base['edges'],
                      raw_tests=base['raw_tests'], tests=tests, max_gates=28,
                      outside_gates=builder.gates, outside_output=output, outside_cost=34,
                      final_or_cost=1, total_if_target_met=63, prefix_orbit_size=orbit['size'],
                      old_supplied_cases=orbit['supplied_cases']))
(HERE/'all-six-prefix-gadgets.json').write_text(json.dumps(cases))
print(dict(cases=len(cases), total_prefix_patterns=sum(c['prefix_orbit_size'] for c in cases),
           outside_costs=sorted({c['outside_cost'] for c in cases}),
           features=sorted({len(c['features']) for c in cases})))
