import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cnf', type=Path, required=True)
    parser.add_argument('--prefix', type=Path, required=True)
    args = parser.parse_args()
    wrapper = Path(__file__).with_name('unique_phased_run.py')
    mapping = args.cnf.with_suffix('.map.json')
    nv = json.loads(mapping.read_text())['nv']
    cases = [
        ('zero', '0\n', 'Zero phase literal', None),
        ('outside', str(nv + 1) + '\n', 'Phase variable outside CNF range', None),
        ('conflict', '1\n-1\n', 'Conflicting phase duplicates', None),
        ('malformed', '1x\n', 'Malformed phase literal', None),
        ('empty', '', 'Empty phase file', None),
        ('nonascii', '\u0661\n', 'Non-ASCII phase data', None),
        ('wrong-cnf-pin', '1\n', 'cnf hash mismatch', 'cnf'),
        ('wrong-map-pin', '1\n', 'map hash mismatch', 'map'),
        ('wrong-phases-pin', '1\n', 'phases hash mismatch', 'phases'),
    ]
    results = []
    for name, contents, expected_error, wrong_pin in cases:
        prefix = Path(str(args.prefix) + '-' + name)
        phases = Path(str(prefix) + '.phases')
        log = Path(str(prefix) + '.log')
        assert not phases.exists() and not log.exists()
        phases.write_text(contents)
        pins = {'cnf': digest(args.cnf), 'map': digest(mapping), 'phases': digest(phases)}
        if wrong_pin:
            pins[wrong_pin] = '0' * 64
        command = [sys.executable, str(wrapper), '--cnf', str(args.cnf), '--phases', str(phases),
                   '--prefix', str(prefix), '--seconds', '1',
                   '--expected-cnf-sha256', pins['cnf'], '--expected-map-sha256', pins['map'],
                   '--expected-phases-sha256', pins['phases']]
        with log.open('w') as stream:
            code = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT).returncode
        assert code != 0 and expected_error in log.read_text()
        forbidden = [Path(str(prefix) + suffix) for suffix in (
            '-run.json', '-result.json', '-solve.log', '-verify.log', '-verified.json', '-witness.json')]
        assert all(not path.exists() for path in forbidden)
        results.append(dict(name=name, command=command, exit_code=code, expected_error=expected_error,
                            rejected_before_launch=True, phase_sha256=digest(phases), log_sha256=digest(log)))
    report = dict(all_passed=True, cases=results, wrapper_sha256=digest(wrapper),
                  source_sha256=digest(Path(__file__)), scope='Nine rejection tests; no solver was launched.')
    output = Path(str(args.prefix) + '-result.json')
    assert not output.exists()
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(all_passed=True, cases=len(results))), flush=True)


if __name__ == '__main__':
    main()
