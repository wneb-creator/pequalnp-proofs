"""Prepare, run, and independently validate candidate-only circuit annealing."""
from pathlib import Path
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
import re
import resource
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path('/tmp/oec/pequalnp-pilot-18')
VALIDATOR = ROOT / 'lean-setup/validate_sat_candidate.py'
VALIDATOR_SHA = 'b807c1a580ce1fa49da51d859e6bc5d94bab2f9f0cd359c35cef35686f826529'
RAW_VALIDATOR = ROOT / 'validate_raw_candidate.py'
RAW_VALIDATOR_SHA = 'd244bfc58d60560041c5890592f3c2de90905c78fcd058f691b27e7785131401'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def validator():
    if digest(VALIDATOR) != VALIDATOR_SHA:
        raise ValueError('Validator hash differs from independently reviewed source')
    spec = importlib.util.spec_from_file_location('reviewed_candidate_validator', VALIDATOR)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def checked_gates(data):
    gates = data['gates']
    if type(gates) is not list or not 1 <= len(gates) <= 22:
        raise ValueError('Expected one through 22 gate descriptions')
    for g, row in enumerate(gates):
        if (type(row) is not list or len(row) != 3 or row[0] not in ('and', 'or')
                or type(row[1]) is not int or type(row[2]) is not int
                or not 0 <= row[1] <= row[2] < 13 + g):
            raise ValueError('Invalid gate or forward reference')
    if type(data['output']) is not int or not 0 <= data['output'] < 13 + len(gates):
        raise ValueError('Invalid output')
    if data['size'] != len(gates):
        raise ValueError('Wrong declared gate count')
    return gates


def prepare(family, output):
    meta = json.loads((family / 'family.json').read_text())
    if not meta['complete'] or meta['samples'] != len(meta['cases']):
        raise ValueError('Incomplete family')
    if not 1 <= meta['samples'] <= 10000:
        raise ValueError('Seed count outside bound')
    check = validator()
    packed = [f'COVER_ANNEAL 1 {meta["samples"]}']
    sources = []
    for entry in meta['cases']:
        if not re.fullmatch(r'c[0-9]{4}-k[0-9]{2}', entry['case']):
            raise ValueError('Invalid baseline name')
        path = family / (entry['case'] + '.baseline22.json')
        if digest(path) != entry['baseline22_sha256']:
            raise ValueError('Baseline hash mismatch')
        data = json.loads(path.read_text())
        gates = checked_gates(data)
        if len(gates) != 22:
            raise ValueError('Seed is not a 22-gate control')
        tables = check.truth_tables(gates, augmented=True)
        check.check_target(tables, data['output'], 'seed baseline')
        packed.append(f'22 {data["output"]}')
        packed.extend(f'{int(op == "and")} {a} {b}' for op, a, b in gates)
        sources.append({'case': entry['case'], 'sha256': digest(path)})
    output.mkdir(parents=True, exist_ok=False)
    pack = output / 'seeds.txt'
    pack.write_text('\n'.join(packed) + '\n')
    write_json(output / 'seeds.json', {
        'kind': 'all2048_checked_22_gate_controls', 'candidate_only': True,
        'assigned_shard_exhaustion': False, 'count': len(sources),
        'family_manifest_sha256': digest(family / 'family.json'),
        'pack_sha256': digest(pack), 'validator_sha256': VALIDATOR_SHA,
        'preparer_sha256': digest(Path(__file__)), 'baselines': sources})
    print(json.dumps({'prepared': str(pack), 'count': len(sources), 'sha256': digest(pack)}))


def run(args):
    if not 0 < args.seconds <= 3600 or not 0 < args.iterations <= 10**12:
        raise ValueError('Time or iteration bound outside supported range')
    if not 100 <= args.restart <= 10**7 or not 1 <= args.weight <= 16 or not 0 <= args.seed < 2**64:
        raise ValueError('Invalid search parameters')
    meta = json.loads(args.pack.with_suffix('.json').read_text())
    if digest(args.pack) != meta['pack_sha256']:
        raise ValueError('Seed pack hash mismatch')
    if digest(RAW_VALIDATOR) != RAW_VALIDATOR_SHA:
        raise ValueError('Raw validator hash differs from reviewed source')
    args.output.mkdir(parents=True, exist_ok=False)
    out = args.output
    command = [str(args.engine.resolve()), '--pack', str(args.pack.resolve()),
               '--output', str((out / 'engine-result.json').resolve()), '--seed', str(args.seed),
               '--seconds', str(args.seconds), '--iterations', str(args.iterations),
               '--restart', str(args.restart), '--weight', str(args.weight)]
    record = {'scope': 'Candidate-only stochastic optimization; no exhaustion claim.',
              'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'engine_sha256': digest(args.engine), 'pack_sha256': digest(args.pack),
              'pack_metadata_sha256': digest(args.pack.with_suffix('.json')),
              'wrapper_sha256': digest(Path(__file__)), 'validator_sha256': RAW_VALIDATOR_SHA,
              'command': command, 'status': 'RUNNING'}
    write_json(out / 'command.json', record)
    stopping = []

    def signal_stop(sig, frame):
        stopping.append(sig)

    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))

    def stop_child(proc):
        if proc.poll() is not None:
            return
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait()

    signal.signal(signal.SIGTERM, signal_stop)
    signal.signal(signal.SIGINT, signal_stop)
    started = time.monotonic()
    proc = None
    try:
        with (out / 'engine.stdout.txt').open('x') as stdout, (out / 'engine.stderr.txt').open('x') as stderr:
            if args.abort_file.exists() or stopping:
                record['status'] = 'ABORTED_BEFORE_START'
            else:
                proc = subprocess.Popen(command, stdout=stdout, stderr=stderr,
                                        preexec_fn=limits, start_new_session=True)
                while proc.poll() is None:
                    if stopping or args.abort_file.exists() or time.monotonic() - started > args.seconds + 5:
                        record['status'] = 'ABORTED'
                        stop_child(proc)
                        break
                    time.sleep(0.1)
                record['engine_exit'] = proc.wait()
        if record['status'] == 'RUNNING':
            result = json.loads((out / 'engine-result.json').read_text())
            record['engine_result_sha256'] = digest(out / 'engine-result.json')
            if record['engine_exit'] == 10 and result['status'] == 'CANDIDATE_NEEDS_INDEPENDENT_VALIDATION':
                with (out / 'validation.stdout.txt').open('x') as va, (out / 'validation.stderr.txt').open('x') as vb:
                    checked = subprocess.run([sys.executable, '-B', str(RAW_VALIDATOR),
                                              str(out / 'engine-result.json'), str(out / 'validated.json')],
                                             stdout=va, stderr=vb, timeout=60)
                record['validator_exit'] = checked.returncode
                if checked.returncode != 0:
                    raise ValueError('Independent all-input validator rejected candidate')
                checked_data = json.loads((out / 'validated.json').read_text())
                if (checked_data['status'] != 'EXACT_AT_MOST_21' or not checked_data['meets_posted_gate_limit']
                        or checked_data['source_sha256'] != digest(out / 'engine-result.json')
                        or checked_data['validator_sha256'] != RAW_VALIDATOR_SHA):
                    raise ValueError('Unexpected independent validation report')
                record['status'] = 'VALIDATED_CANDIDATE_REQUIRES_LEAN'
                record['validated_sha256'] = digest(out / 'validated.json')
            elif record['engine_exit'] == 0 and result['status'] in ('UNKNOWN', 'ABORTED'):
                record['status'] = result['status']
            else:
                raise ValueError('Unexpected engine exit or status')
    except Exception as error:
        record['status'] = 'ERROR'
        record['error_type'] = type(error).__name__
        raise
    finally:
        if proc is not None:
            stop_child(proc)
        record['elapsed_seconds'] = time.monotonic() - started
        record['logs'] = {name: {'sha256': digest(out / name), 'bytes': (out / name).stat().st_size}
                          for name in ('engine.stdout.txt', 'engine.stderr.txt', 'validation.stdout.txt', 'validation.stderr.txt') if (out / name).exists()}
        record['best_files'] = {p.name: digest(p) for p in sorted(out.glob('engine-result.json.best-*.json'))}
        write_json(out / 'result.json', record)
        if record['status'] == 'VALIDATED_CANDIDATE_REQUIRES_LEAN':
            print(str(out / 'validated.json'), flush=True)
        else:
            print(json.dumps({'status': record['status'], 'result': str(out / 'result.json')}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest='command', required=True)
    prep = subs.add_parser('prepare')
    prep.add_argument('family', type=Path)
    prep.add_argument('output', type=Path)
    worker = subs.add_parser('run')
    worker.add_argument('--engine', type=Path, required=True)
    worker.add_argument('--pack', type=Path, required=True)
    worker.add_argument('--output', type=Path, required=True)
    worker.add_argument('--seed', type=int, default=1342)
    worker.add_argument('--seconds', type=float, default=60)
    worker.add_argument('--iterations', type=int, default=100000000)
    worker.add_argument('--restart', type=int, default=100000)
    worker.add_argument('--weight', type=int, default=4)
    worker.add_argument('--abort-file', type=Path, default=ROOT / 'DESK_ERROR.response')
    args = parser.parse_args()
    if args.command == 'prepare':
        prepare(args.family, args.output)
    else:
        run(args)
