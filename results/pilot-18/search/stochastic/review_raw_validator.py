"""Independent bounded controls for the raw circuit validator; no solver."""
from pathlib import Path
import copy
import hashlib
import importlib.util
import json
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path('/tmp/oec/pequalnp-pilot-18')
SOURCE = ROOT / 'validate_raw_candidate.py'
NORMALIZER = ROOT / 'lean-setup/validate_sat_candidate.py'
EXPECTED = 'd244bfc58d60560041c5890592f3c2de90905c78fcd058f691b27e7785131401'
OUT = Path(__file__).parent / 'raw-controls'
OUT.mkdir(exist_ok=False)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SOURCE) == EXPECTED
spec = importlib.util.spec_from_file_location('raw_validator_review_target', SOURCE)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
baseline_path = ROOT / 'cover-neighborhoods-144/c0000-k08.baseline22.json'
baseline = json.loads(baseline_path.read_text())
fixture = OUT / 'known22-offset13.json'
fixture.write_text(json.dumps(baseline) + '\n')
result = module.validate(fixture, NORMALIZER)
assert result['status'] == 'EXACT_BUT_TOO_LARGE' and result['size'] == 22
assert result['meets_posted_gate_limit'] is False and result['requires_Lean_proof']
fixture11 = OUT / 'known22-offset11.json'
fixture11.write_text(json.dumps(result) + '\n')
result11 = module.validate(fixture11, NORMALIZER)
assert result11['gates'] == result['gates'] and result11['output'] == result['output']
assert result11['size'] == 22 and not result11['meets_posted_gate_limit']
mutations = []
for label, change in [
    ('bool-input-count', lambda d: d.update(inputs=True)),
    ('bool-offset', lambda d: d.update(gate_wire_offset=True)),
    ('wrong-offset', lambda d: d.update(gate_wire_offset=12)),
    ('bad-operation', lambda d: d['gates'][0].__setitem__(0, 'xor')),
    ('boolean-source', lambda d: d['gates'][0].__setitem__(1, True)),
    ('negative-source', lambda d: d['gates'][0].__setitem__(1, -1)),
    ('self-reference', lambda d: d['gates'][0].__setitem__(1, 13)),
    ('float-source', lambda d: d['gates'][0].__setitem__(1, 0.0)),
    ('boolean-output', lambda d: d.update(output=True)),
    ('out-of-range-output', lambda d: d.update(output=35)),
    ('false-output', lambda d: d.update(output=11)),
    ('true-output', lambda d: d.update(output=12)),
]:
    data = copy.deepcopy(baseline)
    change(data)
    try:
        module.scalar_check(data)
    except ValueError:
        mutations.append(label)
    else:
        raise AssertionError('Malformed or semantically wrong control accepted: ' + label)
fake = OUT / 'wrong-normalizer.py'
fake.write_text('raise RuntimeError("This source must never be imported")\n')
try:
    module.validate(fixture, fake)
except ValueError as error:
    assert 'hash mismatch' in str(error)
else:
    raise AssertionError('Wrong normalizer accepted')
cli = []
for file in (fixture, fixture11):
    for optimize in (False, True):
        label = file.stem + ('-optimized' if optimize else '-normal')
        command = [sys.executable, '-B'] + (['-O'] if optimize else [])
        command += [str(SOURCE), str(file), str(OUT / (label + '.report.json'))]
        with (OUT / (label + '.stdout.txt')).open('x') as out, (OUT / (label + '.stderr.txt')).open('x') as err:
            proc = subprocess.run(command, stdout=out, stderr=err, timeout=15)
        assert proc.returncode == 2
        cli.append({'label': label, 'exit': proc.returncode})
assert sha(SOURCE) == EXPECTED
review = {
    'verdict': 'PASS', 'source': str(SOURCE), 'source_sha256': EXPECTED,
    'all_source_lines_reviewed': 82,
    'normalizer_sha256': sha(NORMALIZER), 'review_script_sha256': sha(Path(__file__)),
    'controls': {'exact22_offsets13_and11': 2, 'malformed_or_wrong_function_rejections': mutations,
                 'wrong_normalizer_hash_rejected_before_import': True, 'oversized_CLI_controls': cli},
    'reasoning': [
        'Strict integer type checks reject bools, floats, negative wires and forward/self references.',
        'Both offset conventions are evaluated on every one of 2048 assignments using scalar Boolean operations.',
        'Offset-11 gates and output are lifted consistently to the augmented normalizer convention.',
        'The normalizer source is hash-pinned before import; the normalized offset-11 result is independently scalar-evaluated again.',
        'Exit zero requires exact target and normalized size at most 21. Exact 22-gate controls exit two, including under python -O.',
        'No first-junk or two-junk condition is claimed; any accepted candidate still requires Lean verification.'
    ],
    'blocking_findings': [], 'repository_changed': False, 'solver_started': False,
    'scope': 'Validator correctness audit, not a 21-gate candidate or Lean proof.',
    'Sub-agents': 'none'
}
path = ROOT / 'lean-setup/raw-validator-independent-review.json'
path.write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps({'verdict': 'PASS', 'source_sha256': EXPECTED, 'review': str(path), 'review_sha256': sha(path)}))
