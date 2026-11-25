import argparse
import hashlib
import json
import resource
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


SOURCE_SHA = '62f29c9498a6e2d440ad21fde0291a8edc96d7419169c70dfe9795eea898507b'
SOLVER_SHA = 'eb54e117279396bc1d68adb93a60d2d0852054da78f4c06608c47c624e2be9b1'
PRODUCTION_CNF_SHA = '6ff5e62b19607e099ce4c324b20e3a21d9de11da80a76d00a1bc531e9eb65538'
PRODUCTION_MAP_SHA = '5d904111e8cf151235f40dc82f96169b6b0bf08e1370d771b56c41ea65c335a2'


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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cnf', type=Path, required=True)
    parser.add_argument('--prefix', type=Path, required=True)
    parser.add_argument('--seconds', type=int, required=True)
    parser.add_argument('--preset', choices=('default', 'sat', 'unsat'), default='default')
    parser.add_argument('--seed', type=int, default=1)
    parser.add_argument('--expected-cnf-sha256', default=PRODUCTION_CNF_SHA)
    parser.add_argument('--expected-map-sha256', default=PRODUCTION_MAP_SHA)
    parser.add_argument('--solver', type=Path,
                        default=Path('/tmp/oec/pequalnp-pilot-70/circuit-search/kissat/build/kissat'))
    args = parser.parse_args()
    assert args.seconds > 0 and args.seed >= 0
    source = Path(__file__).resolve().with_name('anchored_tail.py')
    mapping = args.cnf.with_suffix('.map.json')
    expected = {'source': (source, SOURCE_SHA), 'solver': (args.solver, SOLVER_SHA),
                'cnf': (args.cnf, args.expected_cnf_sha256),
                'map': (mapping, args.expected_map_sha256)}

    def check_pins():
        for name, (path, wanted) in expected.items():
            assert len(wanted) == 64 and digest(path) == wanted, f'{name} hash mismatch'

    check_pins()
    metadata = json.loads(mapping.read_text())
    assert metadata['cnf_sha256'] == args.expected_cnf_sha256
    assert metadata['source_sha256'] == SOURCE_SHA
    assert metadata['ninputs'] == 14 and len(metadata['rows']) == 58
    assert metadata['anchored_tail']['prefix_gates'] == metadata['gates'] - 2
    assert metadata['anchored_tail']['fixed_tail'] == ['and', 'or']
    paths = {name: Path(str(args.prefix) + suffix) for name, suffix in (
        ('run', '-run.json'), ('result', '-result.json'), ('solve', '-solve.log'),
        ('verify', '-verify.log'), ('verified', '-verified.json'), ('witness', '-witness.json'))}
    assert all(not path.exists() for path in paths.values()), 'Refusing to overwrite a run artifact'
    command = [str(args.solver.resolve()), '-s', f'--time={args.seconds}', f'--seed={args.seed}']
    if args.preset != 'default':
        command.append('--' + args.preset)
    command.append(str(args.cnf.resolve()))
    run = dict(started_at=stamp(), command=command, wall_limit_seconds=args.seconds,
               backend='kissat', preset=args.preset, seed=args.seed,
               gate_count=metadata['gates'], variables=metadata['nv'], clauses=metadata['clauses'],
               wrapper_sha256=digest(Path(__file__)),
               pins={name: {'path': str(path.resolve()), 'sha256': wanted}
                     for name, (path, wanted) in expected.items()},
               scope=metadata['anchored_tail']['scope'])
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
            verify_command = [sys.executable, str(source), 'verify', '--cnf', str(args.cnf.resolve()),
                              '--log', str(paths['solve'].resolve()), '--output', str(paths['verified'].resolve())]
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
            assert verify_code == 0, 'Frozen verifier failed; see complete verification log'
            checked = json.loads(paths['verified'].read_text())
            assert checked['status'] == 'VERIFIED' and checked['checked_assignments'] == 16384
            assert checked['checked_clauses'] == metadata['clauses']
            assert checked['gate_count'] == metadata['gates']
            assert checked['cnf_sha256'] == args.expected_cnf_sha256
            assert checked['source_sha256'] == SOURCE_SHA
            check_pins()
            save(paths['witness'], checked['gates'])
            result.update(full_truth_table_verified=True, checked_clauses=checked['checked_clauses'],
                          checked_assignments=checked['checked_assignments'],
                          verified_file=str(paths['verified'].resolve()),
                          verified_sha256=digest(paths['verified']),
                          witness_file=str(paths['witness'].resolve()),
                          witness_sha256=digest(paths['witness']))
    except Exception as error:
        result.update(status='ERROR', full_truth_table_verified=False, verification_error=repr(error))
    result['finished_at'] = stamp()
    save(paths['result'], result)
    print(json.dumps(result), flush=True)
    return 1 if result['status'] == 'ERROR' else 0


if __name__ == '__main__':
    sys.exit(main())
