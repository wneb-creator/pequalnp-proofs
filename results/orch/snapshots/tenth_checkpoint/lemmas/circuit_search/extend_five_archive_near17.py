"""Hotload independently checked 17-error six-AND phases and graph symmetries."""
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ALG = HERE.parent / 'algebra_strategy'
case = json.loads((ALG / 'five-owner-joint-packet.json').read_text())[0]
assemble = runpy.run_path(str(ALG / 'assemble_five_owner.py'))['assemble_five']
permutations = json.loads((HERE.parent / 'lower_bound/sat/joint_five_owner_symmetry.json').read_text())['permutations']
n, raw = case['inputs'], case['raw_inputs']
supports = [frozenset([i]) for i in range(raw)] + [frozenset(f['raw_indices']) for f in case['features']]
edges = {tuple(edge) for edge in case['edges']}
columns = [int(('1' * (1 << i) + '0' * (1 << i)) * (1 << (raw-i-1)), 2)
           for i in range(raw)]
for feature in case['features']:
    value = 0
    for i in feature['raw_indices']:
        value |= columns[i]
    columns.append(value)
target = 0
for a, b in edges:
    target |= columns[a] & columns[b]
base_names = ['joint-five-drop17-0', 'joint-five-drop17-1', 'joint-five-unfolded17',
              'joint-five-simplified21-error17', 'joint-five-allraw23-error17']
added = []
for name in base_names:
    base = json.loads((HERE / (name+'.json')).read_text())
    for perm in permutations:
        assert sorted(perm) == list(range(n))
        assert {tuple(sorted((perm[a], perm[b]))) for a, b in edges} == edges
        assert all(frozenset(perm[i] for i in support) == supports[perm[j]]
                   for j, support in enumerate(supports))
        gates = [[op, perm[a] if a < n else a, perm[b] if b < n else b] for op, a, b in base]
        _, metadata = assemble(case, gates)
        assert metadata['within_budget']
        values = columns.copy()
        for op, a, b in gates:
            values.append(values[a] | values[b] if op else values[a] & values[b])
        assert target & ~values[-1] == 0 and (values[-1] & ~target).bit_count() == 527
        errors = sum(not label and bool(values[-1] >> mask & 1) for mask, label in case['raw_tests'])
        assert errors == 17
        added.append(dict(gates=gates, source=name, boundary_errors=errors, assembly=metadata))
old = json.loads((HERE / 'joint-five-multiguard-seeds.json').read_text())
combined = added + old
rows = [str(len(combined))]
for seed in combined:
    rows.append(str(len(seed['gates'])))
    rows.extend(' '.join(map(str, gate)) for gate in seed['gates'])
temporary = HERE / 'joint-five-archive-seeds.next.txt'
temporary.write_text('\n'.join(rows)+'\n')
temporary.replace(HERE / 'joint-five-archive-seeds.txt')
(HERE / 'joint-five-archive-near17-seeds.json').write_text(json.dumps(added))
print(dict(added=len(added), total=len(combined), assignments_checked=len(added)*(1 << raw)))
