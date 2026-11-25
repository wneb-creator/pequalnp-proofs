import argparse
import hashlib
import json
import re
import resource
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


VERIFIER_SHA = 'fbdda261ef96bf13ef17d91006cfb85ee0bf1d34363f38f8693c18a8ba0fc391'
HELPER_SHA = '3ba1edbfbc745cca6f0d75a5f0772433a30b6c8feb2cc7f3211f40f3f27615ca'
DRIVER_SHA = '050e6463c4ba26c564d7834021ad75ee40bc16e222cca5aabbf761294b64fa51'
CNF_SHA = '86c036aaf5381cf4d574958b036eb8e32fa257d525fb2e4dd4fa2a33f4c86244'
MAP_SHA = '8451a86887702275a3727555655d708d111d921b5fe0a86daaba7fef62a6b21d'
PHASE_SHA = '5e96bcfb2eba5d129a8b4a0c3b899cb1e6d8d3bdbfba4698ff7cdb50768fa47c'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stamp():
    return datetime.now(timezone.utc).isoformat()


def cpu_usage():
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    return usage.ru_utime + usage.ru_stime, usage.ru_maxrss


def save(path, value):
    assert not path.exists(), f'Output already exists: {path}'
    path.write_text(json.dumps(value, indent=2) + '\n')


def read_phases(path, nv):
    text = path.read_text()
    assert text.isascii(), 'Non-ASCII phase data'
    words = text.split()
    assert words, 'Empty phase file'
    preferences = {}
    for word in words:
        assert re.fullmatch(r'-?[0-9]+', word), 'Malformed phase literal'
        literal = int(word)
        assert literal != 0, 'Zero phase literal'
        variable, value = abs(literal), literal > 0
        assert variable <= nv, 'Phase variable outside CNF range'
        assert variable not in preferences or preferences[variable] == value, 'Conflicting phase duplicates'
        preferences[variable] = value
    return len(words), len(preferences)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cnf', type=Path, required=True)
    parser.add_argument('--phases', type=Path, required=True)
    parser.add_argument('--prefix', type=Path, required=True)
    parser.add_argument('--seconds', type=int, required=True)
    parser.add_argument('--expected-cnf-sha256', default=CNF_SHA)
    parser.add_argument('--expected-map-sha256', default=MAP_SHA)
    parser.add_argument('--expected-phases-sha256', default=PHASE_SHA)
    parser.add_argument('--helper', type=Path,
                        default=Path('/tmp/oec/pequalnp-pilot-70/circuit-search/phased'))
    parser.add_argument('--driver-source', type=Path,
                        default=Path('/tmp/oec/pequalnp-pilot-70/circuit-search/phased.cpp'))
    args = parser.parse_args()
    assert args.seconds > 0
    verifier = Path(__file__).resolve().with_name('raw_verify.py')
    mapping = args.cnf.with_suffix('.map.json')
    expected = {'verifier': (verifier, VERIFIER_SHA), 'helper': (args.helper, HELPER_SHA),
                'driver_source': (args.driver_source, DRIVER_SHA),
                'cnf': (args.cnf, args.expected_cnf_sha256),
                'map': (mapping, args.expected_map_sha256),
                'phases': (args.phases, args.expected_phases_sha256)}

    def check_pins():
        for name, (path, wanted) in expected.items():
            assert len(wanted) == 64 and digest(path) == wanted, f'{name} hash mismatch'

    check_pins()
    metadata = json.loads(mapping.read_text())
    assert metadata['ninputs'] == 14
    with args.cnf.open() as stream:
        header = stream.readline().split()
    assert header == ['p', 'cnf', str(metadata['nv']), str(metadata['clauses'])]
    if 'cnf_sha256' in metadata:
        assert metadata['cnf_sha256'] == args.expected_cnf_sha256
    total_phases, distinct_phases = read_phases(args.phases, metadata['nv'])
    paths = {name: Path(str(args.prefix) + suffix) for name, suffix in (
        ('run', '-run.json'), ('result', '-result.json'), ('solve', '-solve.log'),
        ('verify', '-verify.log'), ('verified', '-verified.json'), ('witness', '-witness.json'))}
    assert all(not path.exists() for path in paths.values()), 'Refusing to overwrite a run artifact'
    command = [str(args.helper.resolve()), str(args.cnf.resolve()), str(args.phases.resolve()), str(args.seconds)]
    run = dict(started_at=stamp(), command=command, solver_limit_seconds=args.seconds,
               backend='cadical-phased', configuration='sat',
               gate_count=metadata['gates'], variables=metadata['nv'], clauses=metadata['clauses'],
               wrapper_sha256=digest(Path(__file__)),
               pins={name: {'path': str(path.resolve()), 'sha256': wanted}
                     for name, (path, wanted) in expected.items()},
               phase_literals=total_phases, distinct_phase_variables=distinct_phases,
               repeated_identical_phase_literals=total_phases - distinct_phases,
               phase_semantics='Soft solver.phase preferences only; no assumptions or added clauses.',
               deadline_semantics='Reviewed helper starts its steady-clock solver deadline after DIMACS parsing.')
    save(paths['run'], run)
    cpu_before, _ = cpu_usage()
    started = time.monotonic()
    with paths['solve'].open('w') as stream:
        code = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT).returncode
    cpu_after, maximum_rss = cpu_usage()
    result = dict(run, solver_finished_at=stamp(), wall_seconds=time.monotonic() - started,
                  cpu_seconds=cpu_after - cpu_before, max_rss_kib=maximum_rss,
                  exit_code=code, status={0: 'UNKNOWN', 10: 'SAT', 20: 'UNSAT'}.get(code, 'ERROR'),
                  solve_log=str(paths['solve'].resolve()), solve_log_sha256=digest(paths['solve']))
    try:
        check_pins()
        if code == 10:
            verify_command = [sys.executable, str(verifier), '--cnf', str(args.cnf.resolve()),
                              '--map', str(mapping.resolve()), '--model', str(paths['solve'].resolve()),
                              '--output', str(paths['verified'].resolve())]
            verify_started = time.monotonic()
            verify_cpu_before, _ = cpu_usage()
            with paths['verify'].open('w') as stream:
                verify_code = subprocess.run(verify_command, stdout=stream, stderr=subprocess.STDOUT).returncode
            verify_cpu_after, verify_rss = cpu_usage()
            result.update(verify_command=verify_command, verification_exit_code=verify_code,
                          verification_wall_seconds=time.monotonic() - verify_started,
                          verification_cpu_seconds=verify_cpu_after - verify_cpu_before,
                          verification_max_rss_kib=verify_rss,
                          verification_log=str(paths['verify'].resolve()),
                          verification_log_sha256=digest(paths['verify']))
            assert verify_code == 0, 'Raw verifier failed; see complete verification log'
            checked = json.loads(paths['verified'].read_text())
            assert checked['status'] == 'VERIFIED' and checked['checked_assignments'] == 16384
            assert checked['checked_clauses'] == metadata['clauses']
            assert checked['gate_count'] == metadata['gates']
            assert checked['cnf_sha256'] == args.expected_cnf_sha256
            assert checked['map_sha256'] == args.expected_map_sha256
            assert checked['model_sha256'] == digest(paths['solve'])
            assert checked['verifier_sha256'] == VERIFIER_SHA
            check_pins()
            save(paths['witness'], checked['gates'])
            result.update(full_truth_table_verified=True, checked_clauses=checked['checked_clauses'],
                          checked_assignments=checked['checked_assignments'],
                          verified_file=str(paths['verified'].resolve()), verified_sha256=digest(paths['verified']),
                          witness_file=str(paths['witness'].resolve()), witness_sha256=digest(paths['witness']))
    except Exception as error:
        result.update(status='ERROR', full_truth_table_verified=False, verification_error=repr(error))
    result['finished_at'] = stamp()
    save(paths['result'], result)
    print(json.dumps(result), flush=True)
    return 1 if result['status'] == 'ERROR' else 0


if __name__ == '__main__':
    sys.exit(main())
