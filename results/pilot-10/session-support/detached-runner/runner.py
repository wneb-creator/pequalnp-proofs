#!/usr/bin/env python3
"""Detached, observable runner for this job's ordinary build and checker only."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone


REPO = Path('/workspace/pequalnp-proofs')
SCRATCH = Path('/tmp/oec/pequalnp-pilot-10')
ENVIRONMENT = SCRATCH / 'toolchain/environment.sh'
DRIVER = Path(__file__).resolve().with_name('command.sh')


def utc():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest_if_available(path):
    try:
        return digest(path)
    except OSError:
        return None


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temporary.replace(path)


def within(path, parent):
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def proc_identity(pid):
    # Read only identity/state metadata, never cmdline, memory, or environment.
    try:
        raw = Path('/proc') / str(pid) / 'stat'
        fields = raw.read_text().rsplit(')', 1)[1].split()
        return {'state': fields[0], 'start_ticks': fields[19], 'pgid': int(fields[2])}
    except (FileNotFoundError, ProcessLookupError):
        return None


def validate_run_dir(value):
    path = Path(value).resolve()
    if not within(path, SCRATCH) or path == SCRATCH:
        raise ValueError('run directory must be below the named job scratch directory')
    return path


def launch(args):
    source = Path(args.source).resolve(strict=True)
    relative = source.relative_to(REPO / 'lean')
    if not re.fullmatch(r'PEqualNP/Outside/L_[A-Za-z0-9_]+\.lean', relative.as_posix()):
        raise ValueError('source must be the named Outside proof file in this repository')
    run_dir = validate_run_dir(args.run_dir)
    if run_dir.exists():
        raise ValueError('run directory already exists; use a new name to preserve all logs')
    statement = None
    if args.kind == 'build':
        command = ['lake', 'build', relative.with_suffix('').as_posix().replace('/', '.')]
        workdir = REPO / 'lean'
    else:
        if args.statement is None:
            raise ValueError('checker requires --statement')
        statement = Path(args.statement).resolve(strict=True)
        if not within(statement, SCRATCH):
            raise ValueError('statement must be in the named job scratch directory')
        command = ['node', 'tools/check-lean.mjs', str(source), str(statement), 'check']
        workdir = REPO
    spec = {
        'kind': args.kind, 'source': str(source), 'source_sha256': digest(source),
        'statement': str(statement) if statement else None,
        'statement_sha256': digest(statement) if statement else None,
        'workdir': str(workdir), 'command': command,
        'environment_script': str(ENVIRONMENT), 'created_utc': utc(),
    }
    run_dir.mkdir(parents=True)
    atomic_json(run_dir / 'spec.json', spec)
    (run_dir / 'source.sha256').write_text(spec['source_sha256'] + '\n')
    with (run_dir / 'runner.stdout').open('xb') as out, (run_dir / 'runner.stderr').open('xb') as err:
        process = subprocess.Popen(
            [sys.executable, str(Path(__file__).resolve()), '_worker', str(run_dir)],
            cwd=REPO, stdin=subprocess.DEVNULL, stdout=out, stderr=err,
            start_new_session=True, close_fds=True,
        )
    value = {'worker_pid': process.pid, 'worker_pgid': process.pid, 'run_dir': str(run_dir)}
    atomic_json(run_dir / 'launch.json', value)
    print(json.dumps(value, sort_keys=True))


def worker(run_dir):
    # A detached session and ignored SIGHUP avoid ordinary terminal/session loss.
    # Host teardown, OOM, SIGKILL, or a sandbox-wide kill can still stop this process.
    signal.signal(signal.SIGHUP, signal.SIG_IGN)
    spec = json.loads((run_dir / 'spec.json').read_text())
    source = Path(spec['source'])
    if digest(source) != spec['source_sha256']:
        raise ValueError('source changed between launch preparation and worker start')
    if spec['statement'] and digest(Path(spec['statement'])) != spec['statement_sha256']:
        raise ValueError('statement changed between launch preparation and worker start')
    started = utc()
    clock = time.monotonic()
    with (run_dir / 'stdout').open('xb', buffering=0) as out, (run_dir / 'stderr').open('xb', buffering=0) as err:
        process = subprocess.Popen(
            ['bash', '--noprofile', '--norc', str(DRIVER), spec['environment_script'],
             spec['workdir'], *spec['command']],
            cwd=spec['workdir'], stdin=subprocess.DEVNULL, stdout=out, stderr=err,
            start_new_session=True, close_fds=True,
        )
        child = proc_identity(process.pid)
        running = {
            'worker_pid': os.getpid(), 'worker_pgid': os.getpgid(0),
            'command_pid': process.pid, 'command_pgid': process.pid,
            'command_start_ticks': child['start_ticks'] if child else None,
            'started_utc': started,
        }
        atomic_json(run_dir / 'running.json', running)
        returncode = process.wait()
    after = digest_if_available(source)
    result = {
        **running, 'ended_utc': utc(), 'elapsed_seconds': time.monotonic() - clock,
        'returncode': returncode, 'source_sha256_before': spec['source_sha256'],
        'source_sha256_after': after, 'source_unchanged': after == spec['source_sha256'],
        'statement_unchanged': (not spec['statement'] or
            digest_if_available(Path(spec['statement'])) == spec['statement_sha256']),
    }
    atomic_json(run_dir / 'result.json', result)
    temporary = run_dir / 'status.tmp'
    temporary.write_text(str(returncode) + '\n')
    temporary.replace(run_dir / 'status')


def cancel(args):
    run_dir = validate_run_dir(args.run_dir)
    if (run_dir / 'result.json').exists():
        raise ValueError('command already completed; no signal sent')
    running = json.loads((run_dir / 'running.json').read_text())
    pid = running['command_pid']
    current = proc_identity(pid)
    if (current is None or current['state'] == 'Z' or
            current['start_ticks'] != running['command_start_ticks'] or
            current['pgid'] != running['command_pgid'] or current['pgid'] != pid):
        raise ValueError('live command identity not verified; no signal sent')
    os.killpg(running['command_pgid'], signal.SIGINT)
    value = {'requested_utc': utc(), 'signal': 'SIGINT', 'command_pgid': running['command_pgid']}
    atomic_json(run_dir / 'cancel-request.json', value)
    print(json.dumps(value, sort_keys=True))


def status(args):
    run_dir = validate_run_dir(args.run_dir)
    value = {'run_dir': str(run_dir)}
    for name in ['launch', 'running', 'result', 'cancel-request', 'runner-error']:
        path = run_dir / (name + '.json')
        if path.exists():
            value[name] = json.loads(path.read_text())
    if 'running' in value:
        value['live_command_identity'] = proc_identity(value['running']['command_pid'])
    print(json.dumps(value, indent=2, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest='action', required=True)
    start = subs.add_parser('launch', help='launch one authorized normal build or checker')
    start.add_argument('--kind', choices=['build', 'checker'], required=True)
    start.add_argument('--source', required=True)
    start.add_argument('--statement')
    start.add_argument('--run-dir', required=True)
    for name in ['status', 'cancel']:
        sub = subs.add_parser(name)
        sub.add_argument('--run-dir', required=True)
    hidden = subs.add_parser('_worker', help=argparse.SUPPRESS)
    hidden.add_argument('run_dir')
    args = parser.parse_args()
    if args.action == '_worker':
        run_dir = validate_run_dir(args.run_dir)
        try:
            worker(run_dir)
        except Exception as error:
            atomic_json(run_dir / 'runner-error.json', {
                'at_utc': utc(), 'type': type(error).__name__, 'message': str(error),
            })
            raise
    else:
        {'launch': launch, 'status': status, 'cancel': cancel}[args.action](args)


if __name__ == '__main__':
    main()
