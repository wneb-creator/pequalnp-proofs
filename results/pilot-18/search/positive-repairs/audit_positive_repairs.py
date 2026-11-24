"""Bounded scalar, exact CNF delta, and synthetic model controls; no solver."""
from pathlib import Path
from collections import deque
import ast
import hashlib
import importlib.util
import json
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path('/tmp/oec/pequalnp-pilot-18')
HERE = ROOT / 'orch/S02'
OUT = HERE / 'positive-controls'
OUT.mkdir(exist_ok=False)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
path = HERE / 'prepare_positive_repairs.py'
spec = importlib.util.spec_from_file_location('positive_source', path)
source = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source)
free, distance, helper, base = source.dependencies()
baseline_path = ROOT / 'lean-setup/cover-neighborhood-controls/reproduced/c0000-k08.baseline22.json'
baseline = json.loads(baseline_path.read_text())
EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]


def evaluate(data, mask, suppress=None):
    values = [bool(mask >> v & 1) for v in range(11)] + [False, True]
    for g, (op, a, b) in enumerate(data['gates']):
        assert op in ('and', 'or') and type(a) is int and type(b) is int and 0 <= a <= b < 13 + g
        values.append(False if suppress == g else (values[a] & values[b] if op == 'and' else values[a] | values[b]))
    return values[data['output']]


target = [any((mask >> a & 1) and (mask >> b & 1) for a, b in EDGES) for mask in range(2048)]
assert all(evaluate(baseline, m) == bool(target[m]) for m in range(2048))
maximal = [m for m in range(2048) if not target[m] and all(m >> v & 1 or target[m | 1 << v] for v in range(11))]
edges = [(1 << a) | (1 << b) for a, b in EDGES]
assert len(edges) == 16 and len(maximal) == 24

# Deterministic synthetic superfunctions: replace one AND by either operand.
# These are known wrong fixtures, not search discoveries or exact witnesses.
fixtures = []
for g, (op, a, b) in enumerate(baseline['gates']):
    if op != 'and':
        continue
    for alias in (a, b):
        def move(w):
            w = alias if w == 13 + g else w
            return w - 1 if w > 13 + g else w
        gates = [[oper, *sorted((move(x), move(y)))] for j, (oper, x, y) in enumerate(baseline['gates']) if j != g]
        data = {'inputs': 11, 'gate_wire_offset': 13, 'gates': gates, 'output': move(baseline['output'])}
        values = [evaluate(data, m) for m in range(2048)]
        assert all(not target[m] or values[m] for m in range(2048))
        fp = [m for m in maximal if values[m]]
        assert fp
        fixtures.append((len(fp), g, alias, data, values))
fixtures.sort(key=lambda r: r[:3])
fp_count, deleted_gate, alias, near, near_values = fixtures[0]
assert fp_count <= 15
near_path = OUT / 'synthetic21-allpositive-not-a-witness.json'
near_path.write_text(json.dumps({**near, 'synthetic_known_wrong_control': True}, indent=2) + '\n')
family = OUT / 'family'
manifest = source.prepare(near_path, family, [2, 3], [3, 5], 15, False)
summary = json.loads((family / 'source-summary.json').read_text())
assert summary['all_positive_edges'] and summary['full_2048_false_negative_count'] == 0
assert summary['boundary_false_positive_masks'] == [m for m in maximal if near_values[m]]
assert summary['full_2048_false_positive_count'] == sum(near_values[m] and not target[m] for m in range(2048))
for row in summary['suppression_impact']:
    for mask in edges + maximal:
        assert source.suppressed_output(near, mask, row['gate']) == evaluate(near, mask, row['gate'])
    assert row['fixed_false_positive_masks'] == [m for m in summary['boundary_false_positive_masks'] if not evaluate(near, m, row['gate'])]
    assert row['lost_positive_edge_masks'] == [m for m in edges if not evaluate(near, m, row['gate'])]

delta_checks = []
for item in manifest['cases']:
    path = family / (item['case'] + '.cnf')
    meta = json.loads(path.with_suffix('.json').read_text())
    assert sha(path) == item['cnf_sha256'] == meta['sha256']
    assert sha(path.with_suffix('.json')) == item['metadata_sha256']
    cnf, original = base.build(size=21, first_junk=0, second_junk=False, prefix_sort=False,
                               last_output=False, live=False, productive_prefix=False)
    marker = [original['junk'][0]]
    assert cnf.clauses.count(marker) == 1
    cnf.clauses.remove(marker)
    if 'budget' in item:
        distance.add_distance(base, cnf, original, near['gates'], item['budget'])
    else:
        for g, (op, a, b) in enumerate(near['gates']):
            if g not in item['free_gates']:
                cnf.clauses += [[original['ops'][g] if op == 'and' else -original['ops'][g]],
                                [original['lefts'][g][a]], [original['rights'][g][b]]]
    assert path.read_bytes() == helper.dimacs(cnf)
    assert not meta['enforce_junk'] and not meta['second_junk'] and not meta['prefix_sort']
    assert not meta['live'] and not meta['productive_prefix'] and not meta['last_output']
    assert meta['output_selection_free'] and 'fixed_output_wire' not in meta
    assert [original['output_selectors'][near['output']]] not in cnf.clauses
    delta_checks.append({'case': item['case'], 'cnf_sha256': sha(path), 'exact_reconstruction': True})

prior = ROOT / 'lean-setup/audit_cover_neighborhoods.py'
assert sha(prior) == 'c95bedc59ed0f48eea883144c6b99c74a8ad5d5942f2ba5a91d8d6843280d90c'
node = next(n for n in ast.parse(prior.read_text()).body if isinstance(n, ast.FunctionDef) and n.name == 'unit_model')
namespace = {'deque': deque}
exec(compile(ast.Module(body=[node], type_ignores=[]), str(prior), 'exec'), namespace)
changed = next(g for g, row in enumerate(baseline['gates']) if row[0] == 'and')
seed_data = json.loads(json.dumps(baseline))
seed_data['gates'][changed][0] = 'or'
seed_data['output'] = 12  # Deliberately wrong free-TRUE output must not be pinned.
dummy_summary = {'negative_repair_gate_order': [changed] + [g for g in range(22) if g != changed]}
models = []
for name, cnf, meta, extra in source.build_cases(free, distance, helper, base, seed_data, dummy_summary, [1], [1]):
    meta['sha256'] = hashlib.sha256(helper.dimacs(cnf)).hexdigest()
    path = OUT / ('known22-' + name + '.cnf')
    path.write_bytes(helper.dimacs(cnf))
    path.with_suffix('.json').write_text(json.dumps(meta, indent=2) + '\n')
    seed = {}
    for g, (op, a, b) in enumerate(baseline['gates']):
        seed[meta['ops'][g]] = op == 'and'
        seed.update({v: i == a for i, v in enumerate(meta['lefts'][g])})
        seed.update({v: i == b for i, v in enumerate(meta['rights'][g])})
        seed[meta['junk'][g]] = False
    seed.update({v: i == baseline['output'] for i, v in enumerate(meta['output_selectors'])})
    seed.update({v: g != changed for g, v in enumerate(meta.get('keep_gate_flags', []))})
    values, unused = namespace['unit_model'](cnf.clauses, cnf.variables, seed)
    assert not values[meta['output_selectors'][12]]
    model = path.with_suffix('.synthetic-model.stdout')
    model.write_text('c Synthetic known22 control; no solver run.\ns SATISFIABLE\nv ' +
                     ' '.join(str(v if values[v] else -v) for v in range(1, cnf.variables + 1)) + ' 0\n')
    with path.with_suffix('.validator.stdout').open('x') as stdout, path.with_suffix('.validator.stderr').open('x') as stderr:
        result = subprocess.run([sys.executable, '-B', str(ROOT / 'lean-setup/validate_sat_candidate.py'), str(path), str(model)],
                                stdout=stdout, stderr=stderr, timeout=30)
    assert result.returncode == 0
    checked = json.loads(path.with_suffix('.validated.json').read_text())
    assert not checked['meets_posted_gate_limit']
    models.append({'case': name, 'validator_exit': 0, 'clauses': len(cnf.clauses), 'gate_limit_met': False,
                   'output_changed_from_TRUE_to_target': True, 'one_gate_changed_back_to_AND': True})

rejections = []
false_seed = ROOT / 'stochastic-candidate-134218/engine-result.json'
for label, source_path, bound in [('misses_edge', false_seed, 15), ('too_many_FP', near_path, fp_count - 1)]:
    assert bound >= 1
    destination = OUT / ('rejected-' + label)
    try:
        source.prepare(source_path, destination, [2], [], bound, False)
    except ValueError as error:
        assert not destination.exists()
        rejections.append({'case': label, 'error': str(error), 'created_output': False})
    else:
        raise AssertionError('Expected rejection')
source.prepare(false_seed, OUT / 'analysis-only', [], [], 15, True)
assert not list((OUT / 'analysis-only').glob('*.cnf'))
analysis = json.loads((OUT / 'analysis-only/source-summary.json').read_text())
assert all(not (set(row['lost_positive_edge_masks']) & set(analysis['boundary_false_negative_masks']))
           for row in analysis['suppression_impact'])
source.prepare(near_path, OUT / 'reproduced', [2, 3], [3, 5], 15, False)
files = sorted(p.name for p in family.iterdir())
assert all((family / name).read_bytes() == (OUT / 'reproduced' / name).read_bytes() for name in files)
review = {'verdict': 'PASS_BOUNDED_SELF_CONTROLS_READY_FOR_MAIN_REVIEW',
    'generator_sha256': sha(HERE / 'prepare_positive_repairs.py'), 'audit_sha256': sha(Path(__file__)),
    'baseline_fixture_sha256': sha(baseline_path), 'synthetic21_fixture_sha256': sha(near_path),
    'family_manifest_sha256': sha(family / 'family.json'),
    'allpositive_synthetic_variants': len(fixtures), 'allinput_scalar_checks': (len(fixtures) + 1) * 2048,
    'fixture_deleted_AND_gate': deleted_gate, 'fixture_alias': alias,
    'fixture_boundary_FP': fp_count, 'fixture_full_FP': summary['full_2048_false_positive_count'],
    'suppression_controls': 21 * 40, 'exact_CNF_deltas': delta_checks, 'known22_models': models,
    'negative_controls': rejections, 'analysis_only_no_CNF': True,
    'byte_identical_reproduction_files': len(files), 'blockers': [],
    'scope': 'Candidate preparation only; synthetic superfunction is wrong, known22 models exceed21; no solver run.'}
path = HERE / 'positive-repairs-review.json'
path.write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps({'review': str(path), 'sha256': sha(path), 'verdict': review['verdict'], 'fixture_boundary_FP': fp_count}))
