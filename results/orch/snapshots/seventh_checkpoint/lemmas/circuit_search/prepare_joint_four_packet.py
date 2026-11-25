import itertools
import json
import pathlib

HERE = pathlib.Path(__file__).resolve().parent
fixed = json.loads((HERE/'context-four-owner-packet.json').read_text())[0]
geometry = json.loads((HERE/'geometry.json').read_text())
neighbors = [{b for a, b in geometry['edges'] if a == p} for p in range(13)]
originals = fixed['input_original']
local = {v: i for i, v in enumerate(originals)}
features, groups, owners = [], [], []
for point in range(13):
    if point in fixed['group']:
        continue
    lines = sorted(neighbors[point] & set(originals[4:]))
    assert len(lines) in (2, 3)
    whole = len(features)
    features.append(dict(original_lines=lines, raw_indices=[local[l] for l in lines],
                         kind='triple' if len(lines) == 3 else 'fixed_pair', outside_owner=point))
    owner = dict(outside_point=point, original_neighbors=sorted(neighbors[point]),
                 core_lines=lines, whole_input=14+whole)
    if len(lines) == 3:
        optional = []
        for pair in itertools.combinations(lines, 2):
            optional.append(14+len(features))
            features.append(dict(original_lines=list(pair), raw_indices=[local[l] for l in pair],
                                 kind='optional_pair', outside_owner=point))
        groups.append(optional)
        owner['optional_inputs'] = optional
    else:
        owner['optional_inputs'] = []
    owners.append(owner)
assert len(features) == 27 and len(groups) == 6
extended = []
for mask, label in fixed['raw_tests']:
    value = mask
    for i, feature in enumerate(features):
        if any(mask >> j & 1 for j in feature['raw_indices']):
            value |= 1 << (14+i)
    extended.append([value, label])
case = dict(name='context_arc_joint_prefixes', group=fixed['group'], raw_inputs=14,
            input_original=originals, inputs=41, features=features, edges=fixed['edges'],
            raw_tests=fixed['raw_tests'], tests=extended, max_gates=18,
            optional_prefix_groups=groups, outside_owners=owners, outside_base_cost=44,
            final_or_cost=1, total_if_target_met=63,
            assembler_metadata=dict(module='assemble_joint_four.py', function='assemble_joint',
                                    budget_rule='active_core_gates + sum(max(used_pairs_in_group - 1, 0)) <= 18'),
            private_raw_indices=[10, 11, 12, 13])
(HERE/'joint-four-owner-packet.json').write_text(json.dumps([case]))
lookup = {frozenset(f['original_lines']): 14+i for i, f in enumerate(features)}
input_map = list(range(14))+[lookup[frozenset(f['original_lines'])] for f in fixed['features']]
seed = json.loads((HERE/'context-four-owner-seed18.json').read_text())
shifted = [[op, input_map[a] if a < 29 else a+12, input_map[b] if b < 29 else b+12]
           for op, a, b in seed]
(HERE/'joint-four-owner-seed18.json').write_text(json.dumps(shifted)+'\n')
print(dict(raw_inputs=14, features=27, inputs=41, optional_prefix_groups=groups,
           outside_base_cost=44, seed_gates=len(shifted)))
