"""Prepare full-plane nonlinear 14-AND starts with all 26 raw inputs mutable."""
import hashlib
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ALG = HERE.parent / 'algebra_strategy'
edges = {tuple(edge) for edge in json.loads((HERE / 'geometry.json').read_text())['edges']}
case = json.loads((HERE / 'full-case.json').read_text())
tests = case['tests'] + [[1 << i, 0] for i in range(26)]
columns = [sum(((mask >> i) & 1) << j for j, (mask, _) in enumerate(tests)) for i in range(26)]
target = sum(label << j for j, (_, label) in enumerate(tests))
guard = sum(1 << j for j, (mask, _) in enumerate(tests)
            if mask.bit_count() == 1 or mask in ((1 << 13)-1, ((1 << 13)-1) << 13))

def evaluate(gates):
    values, line_degree, point_degree = columns.copy(), [int(i >= 13) for i in range(26)], [int(i < 13) for i in range(26)]
    and_depth = [0] * 26
    for i, (op, a, b) in enumerate(gates):
        assert op in (0, 1) and 0 <= a < 26+i and 0 <= b < 26+i
        values.append(values[a] | values[b] if op else values[a] & values[b])
        line_degree.append(max(line_degree[a], line_degree[b]) if op else line_degree[a]+line_degree[b])
        point_degree.append(max(point_degree[a], point_degree[b]) if op else point_degree[a]+point_degree[b])
        and_depth.append(max(and_depth[a], and_depth[b]) + int(op == 0))
    assert values[-1] & target == target and values[-1] & guard == 0
    positive_live = all(values[26+i] & target for i, (op, _, _) in enumerate(gates) if op == 0)
    return (values[-1] & ~target).bit_count(), line_degree[-1], point_degree[-1], positive_live, values[-1], and_depth[-1]

def normalized(terms):
    result = []
    for term in sorted(terms, key=lambda v: (v.bit_count(), v)):
        if not any(prior & term == prior for prior in result):
            result.append(term)
    return frozenset(result)

def dnf(gates, replace=None):
    terms = [frozenset([1 << i]) for i in range(26)]
    for i, (op, a, b) in enumerate(gates):
        if replace is not None and replace[0] == i:
            terms.append(terms[replace[1]])
        else:
            terms.append(normalized(terms[a] | terms[b] if op else {u | v for u in terms[a] for v in terms[b]}))
    return terms[-1]

four_case = json.loads((HERE / 'joint-four-owner-packet.json').read_text())[0]
five_case = json.loads((ALG / 'five-owner-joint-packet.json').read_text())[0]
four_assemble = runpy.run_path(str(HERE / 'assemble_joint_four.py'))['assemble_joint']
five_assemble = runpy.run_path(str(ALG / 'assemble_five_owner.py'))['assemble_five']
raw_sources = [('five_filtered', five_case, five_assemble,
                json.loads((HERE / 'joint-five-initial.json').read_text()))]

def fixed_assemble(packet, core):
    gates = [gate.copy() for gate in packet['outside_gates']]
    mapping = dict(enumerate(packet['input_original']))
    for i, feature in enumerate(packet['features']):
        mapping[packet['raw_inputs']+i] = feature['outside_wire']
    for i, (op, a, b) in enumerate(core):
        gates.append([op, mapping[a], mapping[b]])
        mapping[packet['inputs']+i] = 25+len(gates)
    gates.append([1, packet['outside_output'], mapping[packet['inputs']+len(core)-1]])
    return gates, dict(within_budget=len(gates) <= 63)

six_case = json.loads((HERE / 'six-owner-gadgets.json').read_text())[1]
for index, seed in enumerate(json.loads((HERE / 'feature6-wide-validands.json').read_text())):
    if seed['ands'] == 7:
        raw_sources.append((f'six_wide_{index}', six_case, fixed_assemble, seed['gates']))
for filename in ['full62-seven-and-core.json', 'full63-seven-and-core-19.json',
                 'joint-four-five-best-6-full63.json', 'joint-four-owner-full63.json']:
    full = json.loads((HERE / filename).read_text())
    raw_sources.append((filename, None, lambda _, gates: (gates, dict(within_budget=len(gates) <= 63)), full))
for name, packet, assembler, filename in [
    ('four_multiguard', four_case, four_assemble, 'joint-four-multiguard-seeds.json'),
    ('five_multiguard', five_case, five_assemble, 'joint-five-multiguard-seeds.json'),
]:
    for index, seed in enumerate(json.loads((HERE / filename).read_text())):
        raw_sources.append((f'{name}_{index}', packet, assembler, seed['gates']))

bases, seen = [], set()
for name, packet, assembler, core in raw_sources:
    gates, metadata = assembler(packet, core)
    assert metadata['within_budget'] and len(gates) <= 63
    ands = sum(op == 0 and a != b for op, a, b in gates)
    wrong, line_degree, point_degree, live, signature, and_depth = evaluate(gates)
    assert wrong > 0
    if ands != 14 or not live or and_depth < 2:
        continue
    key = (signature, len(gates))
    if key in seen:
        continue
    seen.add(key)
    bases.append(dict(source=name, gates=gates, boundary_errors=wrong,
                      gate_count=len(gates), and_count=ands,
                      line_degree=line_degree, point_degree=point_degree, and_depth=and_depth))

# Include the best error counts and the smallest active cones, with overlap removed.
ordered = sorted(bases, key=lambda x: (x['boundary_errors'], x['gate_count']))[:16]
ordered += sorted(bases, key=lambda x: (x['gate_count'], x['boundary_errors']))[:16]
ordered += [seed for seed in bases if seed['source'].endswith('.json')]
selected, seen = [], set()
for seed in ordered:
    if seed['source'] in seen:
        continue
    seen.add(seed['source'])
    gates = seed['gates']
    exact_dnf = dnf(gates)
    redundant = [i for i, (op, a, b) in enumerate(gates) if op == 0 and
                 (dnf(gates, (i, a)) == exact_dnf or dnf(gates, (i, b)) == exact_dnf)]
    if redundant:
        continue
    seed['all_ands_output_essential'] = True
    seed['output_dnf_terms'] = len(exact_dnf)
    seed['maximum_output_term_degree'] = max(term.bit_count() for term in exact_dnf)
    selected.append(seed)
assert selected

permutations = []
for multiplier in (1, 3, 9):
    for shift in range(13):
        base = [(multiplier*p+shift) % 13 for p in range(13)]
        base += [13+(multiplier*l-shift) % 13 for l in range(13)]
        for dual in (False, True):
            perm = [(i+13) % 26 if dual else i for i in base]
            assert {tuple(sorted((perm[a], perm[b]))) for a, b in edges} == edges
            permutations.append(perm)

seeds = []
for seed in selected:
    for index, permutation in enumerate(permutations):
        gates = [[op, permutation[a] if a < 26 else a, permutation[b] if b < 26 else b]
                 for op, a, b in seed['gates']]
        wrong, ld, pd, live, _, depth = evaluate(gates)
        assert wrong == seed['boundary_errors'] and depth >= 2 and live
        seeds.append(dict(gates=gates, source=seed['source'], automorphism=index,
                          boundary_errors=wrong, gates_count=len(gates), and_count=14))
rows = [str(len(seeds))]
for seed in seeds:
    rows.append(str(len(seed['gates'])))
    rows.extend(' '.join(map(str, gate)) for gate in seed['gates'])
(HERE / 'global-fourteen-seeds.txt').write_text('\n'.join(rows)+'\n')
(HERE / 'global-fourteen-seeds.json').write_text(json.dumps(seeds))
(HERE / 'global-fourteen-base-seeds.json').write_text(json.dumps(selected))
(HERE / 'global-fourteen-automorphisms.json').write_text(json.dumps(permutations))
(HERE / 'global-fourteen-initial.json').write_text(json.dumps(seeds[0]['gates']))
report = dict(source_circuits=len(raw_sources), eligible_signature_size_classes=len(bases),
              selected_bases=len(selected), automorphisms=len(permutations), seeds=len(seeds),
              minimum_boundary_errors=min(s['boundary_errors'] for s in seeds),
              sizes=sorted({len(s['gates']) for s in seeds}),
              heuristic='MIN_AND14 is a deliberate search profile, not a proved global lower bound.',
              data_sha256=hashlib.sha256((HERE / 'global-fourteen-seeds.json').read_bytes()).hexdigest())
(HERE / 'global-fourteen-preparation.json').write_text(json.dumps(report, indent=2))
print(report)
