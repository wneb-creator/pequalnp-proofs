from pathlib import Path
import copy, hashlib, json, os, resource, subprocess

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path(__file__).resolve().parent
generator = job / 'geometry-meta3773-witness-generate.py'
original = json.loads((job / 'geometry-meta3773-control64.json').read_text())
env = {k: v for k, v in os.environ.items() if k in ('PATH', 'LANG', 'LC_ALL')}
records = []

def check(name, data, flags, valid, output=None):
    candidate = job / ('geometry-witness-test-' + name + '.json')
    candidate.write_text(json.dumps(data, indent=2) + '\n')
    destination = output or job / ('GeometryWitnessTest_' + name + '.lean')
    before = destination.read_bytes() if destination.exists() else None
    command = ['python3', str(generator), '--candidate', str(candidate),
               '--output', str(destination), *flags]
    result = subprocess.run(command, cwd=job, env=env, capture_output=True,
                            text=True, timeout=10)
    (job / ('geometry-witness-test-' + name + '.log')).write_text(result.stdout + result.stderr)
    assert (result.returncode == 0) == valid, (name, result.returncode)
    after = destination.read_bytes() if destination.exists() else None
    if not valid:
        assert after == before, name
    records.append({'case': name, 'exit_code': result.returncode, 'expected_valid': valid,
                    'output_untouched_on_rejection': not valid,
                    'output_sha256': hashlib.sha256(after).hexdigest() if after else None})
    return after

baseline = check('control64', original, ['--control64'], True)
check('default63_rejects64', original, [], False)
short = copy.deepcopy(original); short['gates'].pop(); short['output'] -= 1
check('incorrect63', short, [], False)
badhead = copy.deepcopy(original); badhead['gates'][0][1:] = [4, 5]
check('badhead', badhead, ['--control64'], False)
baddag = copy.deepcopy(original); baddag['gates'][0][1] = 26
check('futurewire', baddag, ['--control64'], False)
badoutput = copy.deepcopy(original); badoutput['output'] -= 1
check('nonlastoutput', badoutput, ['--control64'], False)
badop = copy.deepcopy(original); badop['gates'][0][0] = 2
check('badopcode', badop, ['--control64'], False)
swapped = copy.deepcopy(original); swapped['gates'][0][1:] = [1, 0]
assert check('commutedhead', swapped, ['--control64'], True) == baseline
reversed_ops = copy.deepcopy(original)
for gate in reversed_ops['gates']:
    gate[0] = 1 - gate[0]
assert check('inverseopcodes', reversed_ops, ['--control64', '--and-is-one'], True) == baseline
check('protectedoutput', original, ['--control64'], False, generator)
statement = (job / 'meta3773-statement.txt').read_text().strip().replace('(63 : ℕ)', '(64 : ℕ)')
assert ('theorem PEqualNP.Outside.L_meta_3773_aux.generated_control64 :\n    ' + statement + ' := by\n').encode() in baseline
summary = {'scope': 'Generator validation only; generated Lean still requires compilation.',
           'generator_sha256': hashlib.sha256(generator.read_bytes()).hexdigest(),
           'generated_control_sha256': hashlib.sha256(baseline).hexdigest(),
           'tests': records}
(job / 'geometry-meta3773-witness-tests-result.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary))
