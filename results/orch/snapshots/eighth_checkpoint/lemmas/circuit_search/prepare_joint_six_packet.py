import itertools
import json
import pathlib
import runpy

HERE = pathlib.Path(__file__).resolve().parent
fixed_cases = json.loads((HERE/'six-owner-gadgets.json').read_text())
fixed = fixed_cases[0]
geometry = json.loads((HERE/'geometry.json').read_text())
neighbors = [{b for a, b in geometry['edges'] if a == p} for p in range(13)]
originals = fixed['input_original']
local = {v: i for i, v in enumerate(originals)}
features, groups, owners = [], [], []
for point in range(13):
    if point in fixed['group']:
        continue
    lines = sorted(neighbors[point] & set(originals[6:]))
    assert len(lines) in (2, 3)
    whole = len(features)
    features.append(dict(original_lines=lines, raw_indices=[local[l] for l in lines],
                         kind='triple' if len(lines) == 3 else 'fixed_pair', outside_owner=point))
    owner = dict(outside_point=point, original_neighbors=sorted(neighbors[point]),
                 core_lines=lines, whole_input=17+whole)
    if len(lines) == 3:
        optional = []
        for pair in itertools.combinations(lines, 2):
            optional.append(17+len(features))
            features.append(dict(original_lines=list(pair), raw_indices=[local[l] for l in pair],
                                 kind='optional_pair', outside_owner=point))
        groups.append(optional)
        owner['optional_inputs'] = optional
    else:
        owner['optional_inputs'] = []
    owners.append(owner)
assert len(features) == 25 and len(groups) == 6
extended = []
for mask, label in fixed['raw_tests']:
    value = mask
    for i, feature in enumerate(features):
        if any(mask >> j & 1 for j in feature['raw_indices']):
            value |= 1 << (17+i)
    extended.append([value, label])
case = dict(name='six_owner_joint_prefixes', group=fixed['group'], raw_inputs=17,
            input_original=originals, inputs=42, features=features, edges=fixed['edges'],
            raw_tests=fixed['raw_tests'], tests=extended, max_gates=28,
            optional_prefix_groups=groups, outside_owners=owners, outside_base_cost=34,
            final_or_cost=1, total_if_target_met=63,
            assembler_metadata=dict(module='assemble_joint_four.py', function='assemble_joint',
                                    budget_rule='active_core_gates + sum(max(used_pairs_in_group - 1, 0)) <= 28'))
(HERE/'joint-six-owner-packet.json').write_text(json.dumps([case]))
lookup = {frozenset(f['raw_indices']): 17+i for i, f in enumerate(features)}
raw_perms = json.loads((HERE/'six-prefix-orbits.json').read_text())['raw_input_permutations']
permutations = []
for raw_perm in raw_perms:
    perm = raw_perm+[lookup[frozenset(raw_perm[i] for i in f['raw_indices'])] for f in features]
    assert {tuple(sorted(perm[i] for i in g)) for g in groups} == {tuple(sorted(g)) for g in groups}
    permutations.append(perm)
sources = [(5, 'feature6c5-filtered-merge.json'), (1, 'feature6-full140-restricted.json'),
           (1, 'feature6-context-27g-best-25.json'), (1, 'feature6-seven-best-19.json')]
assemble = runpy.run_path(str(HERE/'assemble_joint_four.py'))['assemble_joint']
seeds, seen = [], set()
for old_index, name in sources:
    source = json.loads((HERE/name).read_text())
    old = fixed_cases[old_index]
    mapping = list(range(17))+[lookup[frozenset(f['raw_indices'])] for f in old['features']]
    shifted = [[op, mapping[a] if a < 30 else a+12, mapping[b] if b < 30 else b+12]
               for op, a, b in source]
    for perm in permutations:
        gates = [[op, perm[a] if a < 42 else a, perm[b] if b < 42 else b] for op, a, b in shifted]
        key = tuple(map(tuple, gates))
        if key in seen:
            continue
        seen.add(key)
        full, report = assemble(case, gates)
        assert report['within_budget']
        seeds.append(dict(gates=gates, source=name, prefix_extra_cost=report['prefix_extra_cost']))
(HERE/'joint-six-seeds.json').write_text(json.dumps(seeds))
lines = [str(len(seeds))]
for seed in seeds:
    lines.append(str(len(seed['gates'])))
    lines.extend(' '.join(map(str, gate)) for gate in seed['gates'])
(HERE/'joint-six-seeds.txt').write_text('\n'.join(lines)+'\n')
tests = extended.copy()
for raw in (1 << i for i in range(17)):
    value = raw
    for j, f in enumerate(features):
        if any(raw >> i & 1 for i in f['raw_indices']):
            value |= 1 << (17+j)
    tests.append([value, 0])
(HERE/'joint-six-tests.txt').write_text(str(len(tests))+'\n'+'\n'.join(f'{x} {y}' for x, y in tests)+'\n')
(HERE/'joint-six-groups.txt').write_text(str(len(groups))+'\n'+'\n'.join(str(len(g))+' '+' '.join(map(str, g)) for g in groups)+'\n')
(HERE/'joint-six-input-symmetries.json').write_text(json.dumps(permutations))
(HERE/'joint-six-initial.json').write_text(json.dumps(seeds[0]['gates'])+'\n')
print(dict(raw_inputs=17, features=25, inputs=42, optional_groups=6,
           outside_base_cost=34, seeds=len(seeds), symmetries=len(permutations)))
