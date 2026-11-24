"""Exact-delta, known22-model and reproducibility controls; no solver calls."""
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
HERE = ROOT / 'lean-setup'
FAMILY = ROOT / 'local-repairs-134218'
OUT = HERE / 'local-repair-controls'
OUT.mkdir(exist_ok=False)
sha = lambda raw: hashlib.sha256(raw).hexdigest()
spec = importlib.util.spec_from_file_location('local_repair_generator', HERE / 'generate_local_repairs.py')
generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)
base = generator.load(ROOT / 'search_l1342_shard17_ancestorreverse.py', 'local_repair_base', generator.BASE_SHA)
manifest = json.loads((FAMILY / 'family.json').read_text())
source = json.loads((FAMILY / 'source.json').read_text())
summary = json.loads((FAMILY / 'source-summary.json').read_text())
assert manifest['complete'] and len(manifest['cases']) == 20
assert manifest['source_sha256'] == sha((FAMILY / 'source.json').read_bytes()) == '3f7e31aa55a515196f4fd7f08905e0a2b08561ab09e6c93a93ae5bc6d202d813'
assert summary == generator.source_summary(source)
assert summary['boundary_false_negative_masks'] == [513] and summary['boundary_false_positive_masks'] == []
assert summary['dead_gates'] == [9]
parent, parent_meta = base.build(size=21, first_junk=0, second_junk=False,
    prefix_sort=False, last_output=False, live=False, productive_prefix=False)
parent_hash = sha(generator.dimacs(parent))
marker = [parent_meta['junk'][0]]
assert parent.clauses.count(marker) == 1
removed = parent.clauses.index(marker)
unchanged = parent.clauses[:removed] + parent.clauses[removed+1:]
cases = []
for entry in manifest['cases']:
    path = FAMILY / (entry['case'] + '.cnf')
    raw = path.read_bytes()
    meta_path = path.with_suffix('.json')
    meta = json.loads(meta_path.read_text())
    assert sha(raw) == entry['cnf_sha256'] == meta['sha256']
    assert sha(meta_path.read_bytes()) == entry['metadata_sha256']
    lines = raw.decode('ascii').splitlines()
    assert lines[0] == f'p cnf {meta["variables"]} {meta["clauses"]}'
    clauses = []
    for line in lines[1:]:
        row = list(map(int, line.split()))
        assert row[-1] == 0 and all(0 < abs(v) <= meta['variables'] for v in row[:-1])
        clauses.append(row[:-1])
    assert len(clauses) == meta['clauses'] and meta['variables'] == parent.variables
    holes = entry['free_gates']
    assert holes == sorted(set(holes)) and 3 <= len(holes) <= 7
    fixed = sorted(set(range(21)) - set(holes))
    pins = []
    for g in fixed:
        op, a, b = source['gates'][g]
        a, b = sorted((a, b))
        pins += [[parent_meta['ops'][g] if op == 'and' else -parent_meta['ops'][g]],
                 [parent_meta['lefts'][g][a]], [parent_meta['rights'][g][b]]]
    pins.append([parent_meta['output_selectors'][source['output']]])
    assert clauses == unchanged + pins
    assert meta['free_gates'] == holes and meta['fixed_gates'] == fixed and meta['pin_clauses'] == pins
    assert meta['base_with_forced_junk_sha256'] == parent_hash
    assert meta['removed_unit_original_index'] == removed and meta['first_junk'] == 0
    assert meta['enforce_junk'] is False and meta['second_junk'] is False
    assert all(meta[key] is False for key in ('prefix_sort', 'live', 'productive_prefix', 'last_output'))
    assert meta['assigned_shard_exhaustion'] is False and meta['candidate_only'] is True
    assert marker not in clauses
    cases.append({'case': entry['case'], 'holes': holes, 'exact_delta': True, 'sha256': sha(raw)})

# Reuse only the previously reviewed pure model-completion function, not the
# enclosing audit's top-level code or filesystem operations.
prior = HERE / 'audit_cover_neighborhoods.py'
assert sha(prior.read_bytes()) == 'c95bedc59ed0f48eea883144c6b99c74a8ad5d5942f2ba5a91d8d6843280d90c'
tree = ast.parse(prior.read_text())
function = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'unit_model')
namespace = {'deque': deque}
exec(compile(ast.Module(body=[function], type_ignores=[]), str(prior), 'exec'), namespace)
unit_model = namespace['unit_model']
baseline = json.loads((ROOT / 'cover-neighborhoods-144/c0000-k08.baseline22.json').read_text())
fixtures = []
for count in range(3, 8):
    holes = list(range(count))
    cnf, meta = generator.repair(base, baseline, holes)
    raw = generator.dimacs(cnf)
    meta['sha256'] = sha(raw)
    meta['control_model_origin'] = 'Synthetic known22 assignment plus unit propagation; no solver was run.'
    path = OUT / f'known22-free{count}.cnf'
    path.write_bytes(raw)
    path.with_suffix('.json').write_text(json.dumps(meta, indent=2) + '\n')
    seed = {}
    for g, (op, a, b) in enumerate(baseline['gates']):
        seed[meta['ops'][g]] = op == 'and'
        seed.update({v: i == a for i, v in enumerate(meta['lefts'][g])})
        seed.update({v: i == b for i, v in enumerate(meta['rights'][g])})
        seed[meta['junk'][g]] = False
    seed.update({v: i == baseline['output'] for i, v in enumerate(meta['output_selectors'])})
    assignment, free = unit_model(cnf.clauses, cnf.variables, seed)
    for g in meta['fixed_gates']:
        changed = dict(assignment)
        changed[meta['ops'][g]] = not changed[meta['ops'][g]]
        assert not all(any(changed[abs(v)] == (v > 0) for v in clause) for clause in meta['pin_clauses'])
    model = OUT / f'known22-free{count}.synthetic-model.stdout'
    model.write_text('c Synthetic known22 control; no solver run.\ns SATISFIABLE\nv ' +
        ' '.join(str(v if assignment[v] else -v) for v in range(1, cnf.variables+1)) + ' 0\n')
    with (OUT / f'known22-free{count}.validator.stdout.txt').open('x') as stdout, (OUT / f'known22-free{count}.validator.stderr.txt').open('x') as stderr:
        checked = subprocess.run([sys.executable, '-B', str(HERE / 'validate_sat_candidate.py'), str(path), str(model)],
                                 stdout=stdout, stderr=stderr, timeout=30)
    assert checked.returncode == 0
    report = json.loads(path.with_suffix('.validated.json').read_text())
    assert report['meets_posted_gate_limit'] is False
    fixtures.append({'free_count': count, 'cnf_sha256': meta['sha256'], 'all_clauses_checked': len(cnf.clauses),
                     'unforced_irrelevant_auxiliaries': free, 'generic_validator_exit': 0,
                     'meets_posted_gate_limit': False, 'no_solver_run': True})
    print(json.dumps(fixtures[-1]), flush=True)

reproduced = OUT / 'reproduced'
generator.generate(ROOT / 'stochastic-candidate-134218/engine-result.json', reproduced,
    ROOT / 'search_l1342_shard17_ancestorreverse.py', 20, 134218, 3, 7)
names = ['source.json', 'source-summary.json', 'family.json']
names += [entry['case'] + extension for entry in manifest['cases'] for extension in ('.cnf', '.json')]
for name in names:
    assert (FAMILY / name).read_bytes() == (reproduced / name).read_bytes()
review = {'verdict': 'PASS_SELF_AUDIT_READY_FOR_MAIN_INDEPENDENT_REVIEW',
    'generator_sha256': sha((HERE / 'generate_local_repairs.py').read_bytes()),
    'audit_sha256': sha(Path(__file__).read_bytes()), 'base_generator_sha256': generator.BASE_SHA,
    'family_manifest_sha256': sha((FAMILY / 'family.json').read_bytes()),
    'source_sha256': manifest['source_sha256'], 'source_summary': summary,
    'case_count': 20, 'cases': cases, 'known22_controls': fixtures,
    'byte_identical_reproduction_files': len(names), 'blocking_findings': [],
    'no_forced_junk_or_clean_prefix': True, 'only_holes_free_and_output_fixed': True,
    'all_original_variable_ids_preserved': True,
    'scope': 'Candidate-only local neighborhoods; no assigned-shard or global exhaustion.',
    'limitations': ['No repair solver was started and no 21-gate witness was found.',
                    'Known22 models are synthetic validation controls, not discoveries.'],
    'Sub-agents': 'none'}
path = HERE / 'local-repair-review.json'
path.write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps({'verdict': review['verdict'], 'review': str(path), 'review_sha256': sha(path.read_bytes()),
    'generator_sha256': review['generator_sha256'], 'formulas': 20, 'controls': 5, 'reproduced_files': len(names)}))
