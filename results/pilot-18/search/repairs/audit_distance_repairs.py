"""Bounded distance-gadget, complete-CNF and unit-refutation controls. No solver."""
from pathlib import Path
from collections import deque
import ast
import hashlib
import importlib.util
import itertools
import json
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path('/tmp/oec/pequalnp-pilot-18')
HERE = ROOT / 'lean-setup'
FAMILY = ROOT / 'distance-repairs-134218'
OUT = HERE / 'distance-repair-controls'
OUT.mkdir(exist_ok=False)
sha = lambda raw: hashlib.sha256(raw).hexdigest()
spec = importlib.util.spec_from_file_location('distance_generator', HERE / 'generate_distance_repairs.py')
generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)
h = generator.helper()
base = h.load(ROOT / 'search_l1342_shard17_ancestorreverse.py', 'distance_review_base', h.BASE_SHA)


def propagate(clauses, initial=None):
    values = dict(initial or {})
    trace = []
    while True:
        changed = False
        for ci, clause in enumerate(clauses):
            if any(abs(lit) in values and values[abs(lit)] == (lit > 0) for lit in clause):
                continue
            unknown = {lit for lit in clause if abs(lit) not in values}
            if not unknown:
                return values, trace, ci
            if len(unknown) == 1:
                literal = next(iter(unknown))
                values[abs(literal)] = literal > 0
                trace.append([literal, ci])
                changed = True
        if not changed:
            return values, trace, None


def read_cnf(path):
    lines = path.read_text().splitlines()
    tag, kind, variables, count = lines[0].split()
    assert tag == 'p' and kind == 'cnf'
    clauses = []
    for line in lines[1:]:
        row = list(map(int, line.split()))
        assert row[-1] == 0 and all(0 < abs(v) <= int(variables) for v in row[:-1])
        clauses.append(row[:-1])
    assert len(clauses) == int(count)
    return int(variables), clauses


source = json.loads((FAMILY / 'source.json').read_text())
source['gates'] = [[op, *sorted((a, b))] for op, a, b in source['gates']]
manifest = json.loads((FAMILY / 'family.json').read_text())
assert manifest['complete'] and [e['budget'] for e in manifest['cases']] == [0, 2, 3, 4, 5]
parent, parent_meta = h.repair(base, source, list(range(21)))
cases = []
keep_controls = 0
for entry in manifest['cases']:
    path = FAMILY / (entry['case'] + '.cnf')
    meta = json.loads(path.with_suffix('.json').read_text())
    variables, clauses = read_cnf(path)
    assert sha(path.read_bytes()) == entry['cnf_sha256'] == meta['sha256']
    assert sha(path.with_suffix('.json').read_bytes()) == entry['metadata_sha256']
    assert meta['unrestricted_repair_parent_sha256'] == sha(h.dimacs(parent))
    assert clauses[:len(parent.clauses)] == parent.clauses
    assert meta['keep_gate_flags'] == list(range(parent.variables + 1, parent.variables + 22))
    expected = []
    for g, keep in enumerate(meta['keep_gate_flags']):
        op, a, b = source['gates'][g]
        match = [parent_meta['ops'][g] if op == 'and' else -parent_meta['ops'][g],
                 parent_meta['lefts'][g][a], parent_meta['rights'][g][b]]
        assert match == meta['keep_gate_match_literals'][g]
        gadget = [[-keep, literal] for literal in match] + [[keep, *[-literal for literal in match]]]
        expected.extend(gadget)
        for mask in range(8):
            for kept in (False, True):
                values = {abs(lit): (bool(mask & (1 << i)) == (lit > 0)) for i, lit in enumerate(match)}
                values[keep] = kept
                satisfies = all(any(values[abs(lit)] == (lit > 0) for lit in c) for c in gadget)
                assert satisfies == (kept == (mask == 7))
                keep_controls += 1
    counter = base.CNF()
    counter.variables = parent.variables + 21
    threshold = base.totalizer_atleast(counter, [-v for v in meta['keep_gate_flags']], entry['budget'] + 1)
    counter.add(-threshold[entry['budget']])
    assert threshold == meta['changed_gate_thresholds']
    assert clauses == parent.clauses + expected + counter.clauses
    assert variables == counter.variables == meta['variables']
    assert meta['enforce_junk'] is False and meta['first_junk'] == 0 and meta['second_junk'] is False
    assert meta['fixed_gates'] == [] and meta['pin_clauses'] == [[meta['output_selectors'][source['output']]]]
    assert meta['candidate_only'] is True and meta['assigned_shard_exhaustion'] is False
    cases.append({'budget': entry['budget'], 'cnf_sha256': meta['sha256'], 'exact_delta': True,
                  'variables': variables, 'clauses': len(clauses)})

signed_controls = 0
for n in range(1, 8):
    for budget in range(n):
        cnf = base.CNF()
        inputs = [cnf.var() for _ in range(n)]
        literals = [v if i % 2 else -v for i, v in enumerate(inputs)]
        threshold = base.totalizer_atleast(cnf, literals, budget + 1)
        cnf.add(-threshold[budget])
        for mask in range(1 << n):
            initial = {v: bool(mask & (1 << i)) for i, v in enumerate(inputs)}
            count = sum(initial[abs(v)] == (v > 0) for v in literals)
            values, trace, conflict = propagate(cnf.clauses, initial)
            assert (conflict is None) == (count <= budget)
            if conflict is None:
                assert len(values) == cnf.variables
                assert all(any(values[abs(v)] == (v > 0) for v in c) for c in cnf.clauses)
            signed_controls += 1

# K=0 fixes the known incorrect 21-gate source. Record and independently replay
# a unit-resolution contradiction for this CONTROL only, not for the gap.
variables, zero_clauses = read_cnf(FAMILY / 'distance-00.cnf')
values, trace, conflict = propagate(zero_clauses)
assert conflict is not None
replay = {}
for literal, ci in trace:
    clause = zero_clauses[ci]
    assert not any(abs(v) in replay and replay[abs(v)] == (v > 0) for v in clause)
    assert {v for v in clause if abs(v) not in replay} == {literal}
    replay[abs(literal)] = literal > 0
assert all(abs(v) in replay and replay[abs(v)] != (v > 0) for v in zero_clauses[conflict])
proof = {'scope': 'Unit-resolution refutation of K=0 wrong-seed CONTROL only.',
         'cnf_sha256': sha((FAMILY / 'distance-00.cnf').read_bytes()),
         'unit_steps': trace, 'conflict_clause_index': conflict}
(OUT / 'k0-unit-refutation.json').write_text(json.dumps(proof, indent=2) + '\n')

prior = HERE / 'audit_cover_neighborhoods.py'
assert sha(prior.read_bytes()) == 'c95bedc59ed0f48eea883144c6b99c74a8ad5d5942f2ba5a91d8d6843280d90c'
function = next(node for node in ast.parse(prior.read_text()).body if isinstance(node, ast.FunctionDef) and node.name == 'unit_model')
namespace = {'deque': deque}
exec(compile(ast.Module(body=[function], type_ignores=[]), str(prior), 'exec'), namespace)
baseline = json.loads((ROOT / 'cover-neighborhoods-144/c0000-k08.baseline22.json').read_text())
fixtures = []
for budget in (0, 2, 5):
    cnf, meta = h.repair(base, baseline, list(range(22)))
    cnf, meta = generator.add_distance(base, cnf, meta, baseline['gates'], budget)
    meta['sha256'] = sha(h.dimacs(cnf))
    meta['control_model_origin'] = 'Synthetic known22 assignment plus unit propagation; no solver run.'
    path = OUT / f'known22-distance{budget}.cnf'
    path.write_bytes(h.dimacs(cnf))
    path.with_suffix('.json').write_text(json.dumps(meta, indent=2) + '\n')
    seed = {v: True for v in meta['keep_gate_flags']}
    for g, (op, a, b) in enumerate(baseline['gates']):
        seed[meta['ops'][g]] = op == 'and'
        seed.update({v: i == a for i, v in enumerate(meta['lefts'][g])})
        seed.update({v: i == b for i, v in enumerate(meta['rights'][g])})
        seed[meta['junk'][g]] = False
    seed.update({v: i == baseline['output'] for i, v in enumerate(meta['output_selectors'])})
    assignment, free = namespace['unit_model'](cnf.clauses, cnf.variables, seed)
    model = OUT / f'known22-distance{budget}.synthetic-model.stdout'
    model.write_text('c Synthetic known22 control; no solver run.\ns SATISFIABLE\nv ' +
        ' '.join(str(v if assignment[v] else -v) for v in range(1, cnf.variables+1)) + ' 0\n')
    with (OUT / f'known22-distance{budget}.validator.stdout.txt').open('x') as stdout, (OUT / f'known22-distance{budget}.validator.stderr.txt').open('x') as stderr:
        proc = subprocess.run([sys.executable, '-B', str(HERE / 'validate_sat_candidate.py'), str(path), str(model)],
                              stdout=stdout, stderr=stderr, timeout=30)
    assert proc.returncode == 0
    report = json.loads(path.with_suffix('.validated.json').read_text())
    assert report['meets_posted_gate_limit'] is False
    fixtures.append({'budget': budget, 'validator_exit': 0, 'all_clauses_checked': len(cnf.clauses),
                     'cnf_sha256': meta['sha256'], 'meets_posted_gate_limit': False})
    print(json.dumps(fixtures[-1]), flush=True)

reproduced = OUT / 'reproduced'
generator.generate(ROOT / 'stochastic-candidate-134218/engine-result.json', reproduced,
                   ROOT / 'search_l1342_shard17_ancestorreverse.py', [0, 2, 3, 4, 5])
names = ['source.json', 'source-summary.json', 'family.json']
names += [entry['case'] + ext for entry in manifest['cases'] for ext in ('.cnf', '.json')]
assert all((FAMILY / name).read_bytes() == (reproduced / name).read_bytes() for name in names)
review = {'verdict': 'PASS_SELF_AUDIT_READY_FOR_MAIN_INDEPENDENT_REVIEW',
    'generator_sha256': sha((HERE / 'generate_distance_repairs.py').read_bytes()),
    'audit_sha256': sha(Path(__file__).read_bytes()), 'local_repair_helper_sha256': generator.HELPER_SHA,
    'base_generator_sha256': h.BASE_SHA, 'family_manifest_sha256': sha((FAMILY / 'family.json').read_bytes()),
    'source_sha256': manifest['source_sha256'], 'cases': cases,
    'exact_keep_equivalence_truth_assignments': keep_controls,
    'signed_totalizer_projection_assignments': signed_controls,
    'k0_wrong_source_unit_refutation': {'replayed': True, 'steps': len(trace),
        'proof_sha256': sha((OUT / 'k0-unit-refutation.json').read_bytes()), 'scope': 'K=0 control only'},
    'known22_controls': fixtures, 'byte_identical_reproduction_files': len(names),
    'reasoning': 'keep_g is equivalent to matching the seed operation and both canonical one-hot operands. The signed counter bounds the number of false keep flags. Thus at most K descriptions change, with arbitrary operations/fanins at changed gates, no clean prefix, no junk units, and the same output selector.',
    'blocking_findings': [], 'scope': 'Candidate-only local repair; no assigned-shard or global exhaustion.',
    'limits': ['No repair solver launched and no 21-gate witness found.',
              'K=0 unit contradiction concerns only the fixed wrong seed; it is not a proof of the posted gap.',
              'Known22 models are synthetic compatibility controls, not discoveries.'], 'Sub-agents': 'none'}
path = HERE / 'distance-repair-review.json'
path.write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps({'verdict': review['verdict'], 'review': str(path), 'review_sha256': sha(path.read_bytes()),
                  'generator_sha256': review['generator_sha256'], 'signed_controls': signed_controls,
                  'keep_controls': keep_controls, 'k0_unit_steps': len(trace)}))
