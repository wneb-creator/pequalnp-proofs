"""Prepare the reviewed five-owner OR-network cost model for stochastic search."""
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ALG = HERE.parent / 'algebra_strategy'
case = json.loads((ALG / 'five-owner-joint-packet.json').read_text())[0]
assemble = runpy.run_path(str(ALG / 'assemble_five_owner.py'))['assemble_five']
raw, inputs = case['raw_inputs'], case['inputs']
groups = [owner for owner in case['outside_owners'] if owner['optional_inputs']]
rows = [str(len(groups))]
for owner in groups:
    indices, costs = owner['optional_inputs'], owner['prefix_extra_cost_table']
    assert len(costs) == 1 << len(indices) and costs[0] == 0
    assert all(costs[mask] <= costs[mask | (1 << bit)]
               for mask in range(len(costs)) for bit in range(len(indices)))
    rows.append(str(len(indices)) + ' ' + ' '.join(map(str, indices)))
    rows.append(' '.join(map(str, costs)))
(HERE / 'joint-five-costs.txt').write_text('\n'.join(rows) + '\n')

tests = list(case['tests'])
for i in range(raw):
    value = 1 << i
    for j, feature in enumerate(case['features']):
        if i in feature['raw_indices']:
            value |= 1 << (raw + j)
    tests.append([value, 0])
(HERE / 'joint-five-tests.txt').write_text(str(len(tests)) + '\n' +
    '\n'.join(f'{x} {y}' for x, y in tests) + '\n')

sources = json.loads((ALG / 'five-owner-joint-seeds.json').read_text())
sources.append(json.loads((ALG / 'five-owner-filtered23-two-feature-phase.json').read_text()))
sources.sort(key=lambda s: (-s['and_count'], s['false_positives']))
perms = json.loads((HERE.parent / 'lower_bound/sat/joint_five_owner_symmetry.json').read_text())['permutations']
seeds, seen = [], set()
for source in sources:
    for perm in perms:
        assert len(perm) == inputs
        gates = [[op, perm[a] if a < inputs else a, perm[b] if b < inputs else b]
                 for op, a, b in source['gates']]
        key = tuple(map(tuple, gates))
        if key in seen:
            continue
        seen.add(key)
        _, metadata = assemble(case, gates)
        assert metadata['within_budget']
        misses = wrong = 0
        for value, expected in case['tests']:
            wire = [(value >> i) & 1 for i in range(inputs)]
            for op, a, b in gates:
                assert op in (0, 1) and 0 <= a < len(wire) and 0 <= b < len(wire)
                wire.append(wire[a] | wire[b] if op else wire[a] & wire[b])
            misses += bool(expected and not wire[-1])
            wrong += bool(not expected and wire[-1])
        assert misses == 0 and wrong > 0
        seeds.append(dict(gates=gates, source=source['source'], and_count=source['and_count'],
                          boundary_errors=wrong, assembly=metadata))
(HERE / 'joint-five-seeds.json').write_text(json.dumps(seeds))
rows = [str(len(seeds))]
for seed in seeds:
    rows.append(str(len(seed['gates'])))
    rows.extend(' '.join(map(str, gate)) for gate in seed['gates'])
(HERE / 'joint-five-seeds.txt').write_text('\n'.join(rows) + '\n')
(HERE / 'joint-five-initial.json').write_text(json.dumps(seeds[0]['gates']))
print(dict(inputs=inputs, raw_inputs=raw, tests=len(tests), seeds=len(seeds),
           min_error=min(s['boundary_errors'] for s in seeds), groups=len(groups),
           first_and_count=seeds[0]['and_count'], source='exact OR-network cost tables'))
