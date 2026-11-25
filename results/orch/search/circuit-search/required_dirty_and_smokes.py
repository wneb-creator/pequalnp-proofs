import hashlib
import json
import subprocess
import sys
from pathlib import Path


BASE = Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
CONSTRUCTIVE = BASE.parent / 'constructive'
sys.path.insert(0, str(CONSTRUCTIVE))
from joint_correlated import generate, load_variants
from joint_smoke import fix, normalize


def command(label, arguments):
    with (BASE / (label + '.log')).open('w') as log:
        result = subprocess.run(arguments, stdout=log, stderr=subprocess.STDOUT)
    assert result.returncode == 0, (label, result.returncode)


variants = load_variants([CONSTRUCTIVE / f'four-star-cut-cone-variant-{i}.json' for i in range(6)])
known = json.loads((CONSTRUCTIVE / 'joint-ten11-smoke-v1-branch-0.verified.json').read_text())['cone_gates']
inputs = variants[0]['data']['cut_inputs']
assert inputs == 18 and len(known) == 11
remap = lambda wire: inputs if wire == 0 else wire if wire < inputs else wire + 1
copied = [['and', 0, 0]] + [[op, remap(a), remap(b)] for op, a, b in known]
copied = normalize(copied, inputs)
assert copied[0] == ['and', 0, 0]
assert any(inputs in (a, b) for _, a, b in copied[1:])
(BASE / 'dirty-and28-smoke-cone.json').write_text(json.dumps(copied, indent=2) + '\n')
positive_base = BASE / 'dirty-and28-smoke-base.cnf'
generate(variants, 12, positive_base)
positive_live = BASE / 'dirty-and28-smoke-live.cnf'
command('dirty-and28-smoke-live-generate', [sys.executable, str(BASE / 'add_correlated_liveness.py'), str(positive_base), str(positive_live)])
positive_dirty = BASE / 'dirty-and28-smoke-dirty.cnf'
command('dirty-and28-smoke-dirty-generate', [sys.executable, str(BASE / 'add_required_dirty_and.py'), str(positive_live), str(positive_dirty)])
positive = BASE / 'dirty-and28-smoke.cnf'
metadata = json.loads(positive_dirty.with_suffix('.map.json').read_text())
fix(positive_dirty, positive, copied, [metadata['variant_selectors'][0]])
command('dirty-and28-smoke-wrapper', [sys.executable, str(CONSTRUCTIVE / 'joint_run.py'), '--cnf', str(positive), '--prefix', str(BASE / 'dirty-and28-smoke'), '--seconds', '5'])
positive_result = json.loads((BASE / 'dirty-and28-smoke-result.json').read_text())
assert positive_result['status'] == 'SAT' and positive_result['full_truth_table_verified']
assert positive_result['full_gate_count'] == 28

negative_base = CONSTRUCTIVE / 'joint-ten11-smoke-v1-base.cnf'
negative_dirty = BASE / 'dirty-and27-clean-smoke-base.cnf'
command('dirty-and27-clean-smoke-generate', [sys.executable, str(BASE / 'add_required_dirty_and.py'), str(negative_base), str(negative_dirty)])
negative = BASE / 'dirty-and27-clean-smoke.cnf'
metadata = json.loads(negative_dirty.with_suffix('.map.json').read_text())
fix(negative_dirty, negative, known, [metadata['variant_selectors'][0]])
command('dirty-and27-clean-smoke-wrapper', [sys.executable, str(CONSTRUCTIVE / 'joint_run.py'), '--cnf', str(negative), '--prefix', str(BASE / 'dirty-and27-clean-smoke'), '--seconds', '5'])
negative_result = json.loads((BASE / 'dirty-and27-clean-smoke-result.json').read_text())
assert negative_result['status'] == 'UNSAT'
report = {'status': 'PASS', 'positive': positive_result, 'negative': negative_result,
          'postprocessor_sha256': hashlib.sha256((BASE / 'add_required_dirty_and.py').read_bytes()).hexdigest(),
          'scope': 'A live AND(raw0,raw0) copy preserves the known target while satisfying dirtiness at28 gates. The fixed clean27 baseline is excluded by the extra condition. No target-budget search.'}
(BASE / 'required-dirty-and-smokes.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'positive_gate_count': 28, 'positive': 'SAT and full truth checked', 'negative_gate_count': 27, 'negative': 'UNSAT'}))
