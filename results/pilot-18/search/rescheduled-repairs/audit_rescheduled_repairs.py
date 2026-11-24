"""Independent scalar/delta/model controls for fresh free-output repairs; no solver."""
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
FAMILY = HERE / 'rescheduled-family'
OUT = HERE / 'rescheduled-controls'
OUT.mkdir(exist_ok=False)
sha = lambda raw: hashlib.sha256(raw).hexdigest()
spec = importlib.util.spec_from_file_location('rescheduled_generator', HERE / 'generate_rescheduled_repairs.py')
generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)
distance, helper, base = generator.dependencies()


def scalar(data, mask):
    values = [bool(mask & (1 << i)) for i in range(11)] + [False, True]
    for i, row in enumerate(data['gates']):
        op, a, b = row
        assert op in ('and', 'or') and type(a) is int and type(b) is int and 0 <= a <= b < 13 + i
        values.append(values[a] and values[b] if op == 'and' else values[a] or values[b])
    assert 0 <= data['output'] < len(values)
    return values


manifest = json.loads((FAMILY / 'family.json').read_text())
assert manifest['complete'] and len(manifest['sources']) == 2
assert len(manifest['variants']) == 12 and len(manifest['cases']) == 24
sources = []
for entry in manifest['sources']:
    path = FAMILY / entry['file']
    assert sha(path.read_bytes()) == entry['sha256']
    sources.append(json.loads(path.read_text()))
assert [entry['sha256'] for entry in manifest['sources']] == [
    '3f7e31aa55a515196f4fd7f08905e0a2b08561ab09e6c93a93ae5bc6d202d813',
    '902ffe64e011f937c9e46372c2133c7c8fd75494d459149fc9e33ed9661f821a']
variants = {}
scalar_gate_checks = 0
for entry in manifest['variants']:
    path = FAMILY / (entry['variant'] + '.seed.json')
    assert sha(path.read_bytes()) == entry['sha256']
    variant = json.loads(path.read_text())
    source = sources[entry['source_index']]
    mapping = {int(k): v for k, v in entry['old_to_new_gate'].items()}
    assert set(mapping) == set(range(21)) and set(mapping.values()) == set(range(21))
    live = set()
    if source['output'] >= 13:
        live.add(source['output'] - 13)
    for g in range(20, -1, -1):
        if g in live:
            live.update(w - 13 for w in source['gates'][g][1:] if w >= 13)
    assert len(live) == 20 and set(range(21)) - live == {entry['old_dead_gate']}
    assert mapping[entry['old_dead_gate']] == entry['dead_position']
    assert variant['output'] == 13 + mapping[source['output'] - 13]
    edge = tuple(entry['replacement_edge'])
    assert edge in helper.EDGES
    for mask in range(2048):
        before, after = scalar(source, mask), scalar(variant, mask)
        assert before[source['output']] == after[variant['output']]
        assert all(before[13 + old] == after[13 + mapping[old]] for old in live)
        assert after[13 + entry['dead_position']] == bool(mask & (1 << edge[0]) and mask & (1 << edge[1]))
        scalar_gate_checks += 20
    variants[entry['variant']] = variant

cases = []
for entry in manifest['cases']:
    path = FAMILY / (entry['case'] + '.cnf')
    raw = path.read_bytes()
    meta = json.loads(path.with_suffix('.json').read_text())
    assert sha(raw) == entry['cnf_sha256'] == meta['sha256']
    assert sha(path.with_suffix('.json').read_bytes()) == entry['metadata_sha256']
    variant = variants[entry['variant']]
    cnf, expected_meta = helper.repair(base, variant, list(range(21)))
    assert meta['output_pinned_parent_sha256'] == sha(helper.dimacs(cnf))
    marker = [expected_meta['output_selectors'][variant['output']]]
    assert cnf.clauses[-1] == marker and cnf.clauses.count(marker) == 1
    assert meta['removed_output_pin_index'] == len(cnf.clauses) - 1
    cnf.clauses.pop()
    cnf, expected_meta = distance.add_distance(base, cnf, expected_meta, variant['gates'], entry['budget'])
    assert raw == helper.dimacs(cnf)
    assert meta['output_selection_free'] is True and meta['pin_clauses'] == [] and 'fixed_output_wire' not in meta
    assert meta['last_output'] is False and meta['first_junk'] == 0 and meta['enforce_junk'] is False
    assert meta['candidate_only'] is True and meta['assigned_shard_exhaustion'] is False
    assert meta['keep_gate_flags'] == expected_meta['keep_gate_flags']
    assert meta['keep_gate_match_literals'] == expected_meta['keep_gate_match_literals']
    assert meta['changed_gate_thresholds'] == expected_meta['changed_gate_thresholds']
    assert marker not in cnf.clauses
    cases.append({'case': entry['case'], 'cnf_sha256': meta['sha256'], 'exact_output_pin_removal_and_reviewed_distance_delta': True})

prior = ROOT / 'lean-setup/audit_cover_neighborhoods.py'
assert sha(prior.read_bytes()) == 'c95bedc59ed0f48eea883144c6b99c74a8ad5d5942f2ba5a91d8d6843280d90c'
function = next(node for node in ast.parse(prior.read_text()).body if isinstance(node, ast.FunctionDef) and node.name == 'unit_model')
namespace = {'deque': deque}
exec(compile(ast.Module(body=[function], type_ignores=[]), str(prior), 'exec'), namespace)
baseline = json.loads((ROOT / 'cover-neighborhoods-144/c0000-k08.baseline22.json').read_text())
correct_output = baseline['output']
controls = []
for budget in (0, 4):
    # An intentionally wrong FALSE source output must not constrain the new
    # output selector. Exact gate descriptions are unchanged and remain clean.
    seed_data = dict(baseline, output=11)
    cnf, meta = generator.unrestricted_distance(distance, helper, base, seed_data, budget)
    meta['sha256'] = sha(helper.dimacs(cnf))
    meta['control_model_origin'] = 'Synthetic known22 model with correct output different from seed FALSE; no solver run.'
    path = OUT / f'known22-freeoutput-k{budget}.cnf'
    path.write_bytes(helper.dimacs(cnf))
    path.with_suffix('.json').write_text(json.dumps(meta, indent=2) + '\n')
    seed = {v: True for v in meta['keep_gate_flags']}
    for g, (op, a, b) in enumerate(baseline['gates']):
        seed[meta['ops'][g]] = op == 'and'
        seed.update({v: i == a for i, v in enumerate(meta['lefts'][g])})
        seed.update({v: i == b for i, v in enumerate(meta['rights'][g])})
        seed[meta['junk'][g]] = False
    seed.update({v: i == correct_output for i, v in enumerate(meta['output_selectors'])})
    assignment, free = namespace['unit_model'](cnf.clauses, cnf.variables, seed)
    assert assignment[meta['output_selectors'][11]] is False
    assert not any(assignment[abs(v)] == (v > 0) for v in meta['removed_output_pin'])
    model = OUT / f'known22-freeoutput-k{budget}.synthetic-model.stdout'
    model.write_text('c Synthetic known22 free-output control; no solver run.\ns SATISFIABLE\nv ' +
        ' '.join(str(v if assignment[v] else -v) for v in range(1, cnf.variables+1)) + ' 0\n')
    with (OUT / f'known22-freeoutput-k{budget}.validator.stdout.txt').open('x') as stdout, (OUT / f'known22-freeoutput-k{budget}.validator.stderr.txt').open('x') as stderr:
        proc = subprocess.run([sys.executable, '-B', str(ROOT / 'lean-setup/validate_sat_candidate.py'), str(path), str(model)],
                              stdout=stdout, stderr=stderr, timeout=30)
    assert proc.returncode == 0
    report = json.loads(path.with_suffix('.validated.json').read_text())
    assert report['meets_posted_gate_limit'] is False
    controls.append({'budget': budget, 'seed_output': 11, 'model_output': correct_output,
                     'generic_validator_exit': 0, 'all_clauses_checked': len(cnf.clauses),
                     'restoring_old_output_pin_rejects_model': True, 'meets_posted_gate_limit': False})
    print(json.dumps(controls[-1]), flush=True)

reproduced = OUT / 'reproduced'
generator.generate([ROOT / 'stochastic-candidate-134218/engine-result.json', ROOT / 'stochastic-candidate-134219/engine-result.json'],
                   reproduced, 134222, [4, 5])
names = ['family.json'] + [e['file'] for e in manifest['sources']]
names += [e['variant'] + '.seed.json' for e in manifest['variants']]
names += [e['case'] + ext for e in manifest['cases'] for ext in ('.cnf', '.json')]
assert all((FAMILY / name).read_bytes() == (reproduced / name).read_bytes() for name in names)
review = {'verdict': 'PASS_SELF_AUDIT_READY_FOR_MAIN_INDEPENDENT_REVIEW',
    'generator_sha256': sha((HERE / 'generate_rescheduled_repairs.py').read_bytes()),
    'audit_sha256': sha(Path(__file__).read_bytes()), 'distance_helper_sha256': generator.DISTANCE_SHA,
    'local_helper_sha256': distance.HELPER_SHA, 'base_generator_sha256': helper.BASE_SHA,
    'family_manifest_sha256': sha((FAMILY / 'family.json').read_bytes()),
    'source_count': 2, 'variant_count': 12, 'case_count': 24,
    'all2048_live_gate_value_comparisons': scalar_gate_checks,
    'all2048_output_comparisons': 12 * 2048, 'cases': cases, 'free_output_known22_controls': controls,
    'byte_identical_reproduction_files': len(names), 'blocking_findings': [],
    'scope': 'Fresh candidate-only multi-source, rescheduled, unrestricted-output local repairs; no global or assigned-shard exhaustion.',
    'limits': ['No search worker launched and no21-gate exact witness found.',
              'Output selection is free and is not charged to the gate-description edit budget.',
              'Topological rescheduling preserves the incomplete seed function, not a claimed WLOG reduction of all target circuits.',
              'Known22 models are synthetic controls, not discoveries.'], 'Sub-agents': 'none'}
path = HERE / 'rescheduled-review.json'
path.write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps({'verdict': review['verdict'], 'review': str(path), 'review_sha256': sha(path.read_bytes()),
                  'generator_sha256': review['generator_sha256'], 'cases': 24, 'variants': 12,
                  'scalar_gate_checks': scalar_gate_checks, 'reproduced_files': len(names)}))
