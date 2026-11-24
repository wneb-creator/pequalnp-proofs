"""Bounded controller controls using fake completed engines; no search worker."""
from pathlib import Path
import copy
import importlib.util
import json
import subprocess
import sys
import types

sys.dont_write_bytecode = True
HERE = Path(__file__).parent
OUT = HERE / 'wrapper-controls'
OUT.mkdir(exist_ok=False)
spec = importlib.util.spec_from_file_location('stochastic_wrapper_under_test', HERE / 'stochastic_tools.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
baseline = json.loads((HERE.parent.parent / 'cover-neighborhoods-144/c0000-k08.baseline22.json').read_text())
controls = []


def test(label, code, engine_status, payload, expected, abort=False):
    folder = OUT / label
    args = types.SimpleNamespace(seconds=1.0, iterations=1, restart=100, weight=4, seed=7,
        pack=HERE / 'seed-pack/seeds.txt', output=folder, engine=HERE / 'circuit_anneal',
        abort_file=OUT / (label + '.abort'))
    calls = []
    if abort:
        args.abort_file.write_text('Control sentinel, no lease data.\n')

    class FakeFinishedEngine:
        pid = -1  # Never used: poll() always reports an already-exited child.

        def __init__(self, command, stdout, stderr, **kwargs):
            calls.append(command)
            data = copy.deepcopy(payload)
            data['status'] = engine_status
            path = Path(command[command.index('--output') + 1])
            path.write_text(json.dumps(data) + '\n')
            stdout.write('Synthetic completed-engine control; no solver or optimizer invoked.\n')
            stdout.flush()
            stderr.write('')

        def poll(self):
            return code

        def wait(self, timeout=None):
            return code

    module.subprocess = types.SimpleNamespace(Popen=FakeFinishedEngine,
        run=subprocess.run, TimeoutExpired=subprocess.TimeoutExpired)
    raised = False
    try:
        module.run(args)
    except ValueError:
        raised = True
    result = json.loads((folder / 'result.json').read_text())
    assert result['status'] == expected
    assert raised == (expected == 'ERROR')
    if abort:
        assert not calls and 'engine_exit' not in result
    else:
        assert len(calls) == 1 and result['engine_exit'] == code
    if code == 10 and engine_status == 'CANDIDATE_NEEDS_INDEPENDENT_VALIDATION' and not abort:
        assert result['validator_exit'] == 2
        assert (folder / 'validation.stdout.txt').is_file()
        assert (folder / 'validation.stderr.txt').is_file()
    controls.append({'label': label, 'status': result['status'], 'real_search_engine_started': False})


unknown = copy.deepcopy(baseline)
unknown['gates'] = unknown['gates'][:21]
unknown.update(size=21, output=33)
test('unknown', 0, 'UNKNOWN', unknown, 'UNKNOWN')
test('aborted-engine', 0, 'ABORTED', unknown, 'ABORTED')
test('exit-error', 2, 'UNKNOWN', unknown, 'ERROR')
test('exit10-wrong-status', 10, 'UNKNOWN', unknown, 'ERROR')
test('known22-never-a-witness', 10, 'CANDIDATE_NEEDS_INDEPENDENT_VALIDATION', baseline, 'ERROR')
wrong = copy.deepcopy(unknown)
wrong['output'] = 11
test('wrong21-never-a-witness', 10, 'CANDIDATE_NEEDS_INDEPENDENT_VALIDATION', wrong, 'ERROR')
test('preexisting-abort-starts-nothing', 0, 'UNKNOWN', unknown, 'ABORTED_BEFORE_START', abort=True)
(OUT / 'review.json').write_text(json.dumps({'status': 'PASS', 'controls': controls,
    'scope': 'Fake completed-engine controls; real raw-validator subprocesses only. No stochastic search.'}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'controls': len(controls), 'real_search_engine_started': False}))
