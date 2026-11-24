"""Independent finite semantics and exact added-unit audit; no solver/build."""
from pathlib import Path
import hashlib
import importlib.util
import itertools
import json

ROOT = Path('/tmp/oec/pequalnp-pilot-18')
HERE = ROOT / 'orch/S02'
OUT = HERE / 'triangle-controls'
OUT.mkdir(exist_ok=False)
FAMILY = HERE / 'triangle-upper-factors'
PARENT = ROOT / 'orch/S01/consecutive-junk-v2/normalized.cnf'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source = HERE / 'generate_triangle_factors.py'
spec = importlib.util.spec_from_file_location('triangle_generator', source)
generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)
parent_raw = PARENT.read_bytes()
parent = json.loads(PARENT.with_suffix('.json').read_text())
assert sha(PARENT) == '3fefefe3949bc703fc2b9f023be12bc42f1afe7619e8ed5ed63be2f8e7648812'
assert sha(PARENT.with_suffix('.json')) == 'a7425759cf64d1eef6ccd281dedf0c2e67049b88ce335a4ac166fcc0d077e19b'
parent_body = parent_raw.split(b'\n', 1)[1]
manifest = json.loads((FAMILY / 'family.json').read_text())
assert manifest['complete'] and manifest['program_sha256'] == sha(source)
assert len(manifest['cases']) == 12 and manifest['cost_feasible_case_count'] == 6
edges = {(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)}
adjacency = {v: {u for u in range(11) if (min(v,u),max(v,u)) in edges} for v in range(11)}
triangles = [(1,4,8),(3,6,7)]
assert adjacency[1] == {4,8} and adjacency[3] == {6,7}
positives, factor_values, negative_masks = [], {v: [] for t in triangles for v in t}, []
for mask in range(2048):
    vertices = {v for v in range(11) if mask & (1 << v)}
    positive = any({a,b} <= vertices for a,b in edges)
    positives.append(positive)
    if not positive:
        negative_masks.append(mask)
    for v in factor_values:
        value = positive or bool(vertices & adjacency[v])
        assert value == generator.factor(mask,v)
        factor_values[v].append(value)
    for triangle in triangles:
        assert all(factor_values[v][-1] for v in triangle) == positive
assert len(negative_masks) == 125
maximal = [m for m in negative_masks if all(m & (1 << v) or positives[m | (1 << v)] for v in range(11))]
assert parent['rows'][16:] == maximal and len(maximal) == 24

costs = {}
for v in factor_values:
    support = adjacency[v]
    residual = [(a,b) for a,b in sorted(edges) if a not in support and b not in support]
    active = sorted(set().union(*(set(e) for e in residual)))
    covers = next([list(c) for c in itertools.combinations(active,k)
                   if all(a in c or b in c for a,b in residual)]
                  for k in range(len(active)+1)
                  if any(all(a in c or b in c for a,b in residual) for c in itertools.combinations(active,k)))
    tau = len(covers[0])
    costs[v] = len(support)+len(residual)+tau-1
    expected = manifest['factor_costs'][str(v)]
    assert expected['support'] == sorted(support) and expected['residual_cover_size'] == tau
    assert expected['clean_wire_gate_lower_bound'] == costs[v]
    assert costs[v] == parent['support_cost_bounds'][sum(1 << u for u in support)]

expected_orders = {(t,p) for t in triangles for p in itertools.permutations(t)}
seen = set()
cases, unit_controls, suffix_rows = [], 0, 0
for item in manifest['cases']:
    triangle, order = tuple(item['triangle']), tuple(item['order'])
    assert (triangle,order) in expected_orders and (triangle,order) not in seen
    seen.add((triangle,order))
    path = FAMILY / (item['case'] + '.cnf')
    raw = path.read_bytes()
    child = json.loads(path.with_suffix('.json').read_text())
    assert sha(path) == item['cnf_sha256'] == child['sha256']
    assert sha(path.with_suffix('.json')) == item['metadata_sha256']
    expected_units = []
    assignment = {}
    for g,vertex in zip((14,15,16),order):
        wire = 13+g
        for bit, literal in enumerate(parent['prefix_support_tables'][wire]):
            truth = factor_values[vertex][1 << bit]
            assert truth == (bit in adjacency[vertex])
            signed = literal if truth else -literal
            expected_units.append([signed]);assignment[abs(literal)] = signed > 0
        for row,literal in zip(parent['rows'][:16],parent['prefix_edge_tables'][wire]):
            assert factor_values[vertex][row]
            expected_units.append([literal]);assignment[abs(literal)] = literal > 0
    suffix = [(27,27),(30,30),(28,31),(29,32)]
    for g,(left,right) in zip(range(17,21),suffix):
        for literal in [parent['ops'][g],parent['lefts'][g][left],parent['rights'][g][right]]:
            expected_units.append([literal]);assignment[literal] = True
    assert len(expected_units) == len(assignment) == 93
    assert child['triangle_factor_added_units'] == expected_units
    addition = ''.join(str(c[0])+' 0\n' for c in expected_units).encode()
    assert raw == b'p cnf 11968 114660\n' + parent_body + addition
    for clause in expected_units:
        literal = clause[0]
        assert assignment[abs(literal)] == (literal > 0)
        assert (not assignment[abs(literal)]) != (literal > 0)
        unit_controls += 1
    feasible = all(costs[v] <= 15+i for i,v in enumerate(order))
    assert feasible == item['cost_feasible'] == child['triangle_factor_cost_feasible']
    assert child['candidate_only'] and not child['assigned_shard_exhaustion'] and not child['triangle_factor_claimed_WLOG']
    assert child['first_junk'] == 17 and child['second_junk'] and child['consecutive_junk']
    assert child['original_DAG'] and child['live'] and child['last_output'] and child['prefix_sort'] and child['prefix_lex']
    assert child['triangle_factor_boundary_values'] == [[factor_values[v][mask] for mask in parent['rows']] for v in order]
    # Evaluate actual chain wire references using exact factors as prefix oracles.
    # This checks the suffix and unit interpretation, not existence of a17gate prefix.
    values = {27+i:factor_values[v] for i,v in enumerate(order)}
    for g,(a,b) in zip(range(17,21),suffix):
        values[13+g] = [x and y for x,y in zip(values[a],values[b])]
    assert values[33] == positives
    assert all(any(values[13+g][m] for m in negative_masks) for g in (17,18,19))
    assert not any(values[33][m] for m in negative_masks)
    assert {30,31,32} <= {w for pair in suffix for w in pair}
    suffix_rows += 2048
    cases.append({'case':item['case'],'cnf_sha256':sha(path),'metadata_sha256':sha(path.with_suffix('.json')),
                  'parent_body_preserved':True,'exact_93_unit_delta':True,'cost_feasible':feasible})
assert seen == expected_orders
assert sum(c['cost_feasible'] for c in cases) == 6

# Mutation controls must reject before writing any output directory.
bad_parent = OUT / 'bad-parent.cnf'
bad_parent.write_bytes(parent_raw.replace(b'p cnf',b'c cnf',1))
bad_parent.with_suffix('.json').write_bytes(PARENT.with_suffix('.json').read_bytes())
try:
    generator.generate(bad_parent, OUT / 'bad-parent-output')
except ValueError as error:
    assert 'SHA256 mismatch' in str(error) and not (OUT / 'bad-parent-output').exists()
else:
    raise AssertionError('Wrong parent accepted')
try:
    generator.generate(PARENT,FAMILY)
except ValueError as error:
    assert 'fresh' in str(error)
else:
    raise AssertionError('Existing output accepted')
reproduced = OUT / 'reproduced'
generator.generate(PARENT,reproduced)
files = sorted(p.name for p in FAMILY.iterdir())
assert len(files) == 25 and all((FAMILY/n).read_bytes() == (reproduced/n).read_bytes() for n in files)
assert sha(source) == manifest['program_sha256'] and sha(PARENT) == generator.PARENT_SHA
review = {'verdict':'PASS_SELF_AUDIT_READY_FOR_MAIN_REVIEW','generator_sha256':sha(source),
    'audit_sha256':sha(Path(__file__)),'family_manifest_sha256':sha(FAMILY/'family.json'),
    'parent_sha256':sha(PARENT),'parent_metadata_sha256':sha(PARENT.with_suffix('.json')),
    'case_count':12,'cost_feasible_cases':6,'factor_scalar_checks':6*2048,
    'factor_product_checks':2*2048,'full_suffix_row_checks':suffix_rows,
    'added_unit_controls':unit_controls,'costs':costs,'cases':cases,
    'negative_controls':['mutated_parent_hash_rejected_before_output','existing_directory_rejected'],
    'byte_identical_reproduction_files':25,'blocking_findings':[],
    'limitations':['No SAT model is known; abstract factor oracles validate the suffix but not17gate simultaneous prefix realizability.',
                   'Fixed last-three output locations, exact factors and every inherited parent cut restrict a candidate family; no WLOG or exhaustion claim.',
                   'Six bound-infeasible permutations remain generated for audit and should not receive candidate runtime.',
                   'No solver, worker, Lean build, repository change or desk request occurred.']}
path = HERE/'triangle-factor-review.json'
path.write_text(json.dumps(review,indent=2)+'\n')
print(json.dumps({'review':str(path),'sha256':sha(path),'verdict':review['verdict'],
                  'cases':12,'cost_feasible':6,'source_sha256':sha(source)}))
