import argparse
import datetime
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def write_status(path, data):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(data, indent=2) + '\n')
    temporary.replace(path)


parser = argparse.ArgumentParser()
parser.add_argument('--stem', required=True)
parser.add_argument('--solver', required=True)
parser.add_argument('--seconds', type=int, default=900)
parser.add_argument('--worker', action='store_true')
args = parser.parse_args()
stem = Path(args.stem)
if not args.worker:
    with open(str(stem) + '-supervisor.log', 'wb') as log:
        worker = subprocess.Popen([sys.executable, __file__, '--worker', '--stem', args.stem,
            '--solver', args.solver, '--seconds', str(args.seconds)],
            stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
            start_new_session=True, close_fds=True)
    print(json.dumps({'supervisor_pid': worker.pid, 'stem': args.stem}))
else:
    signal.signal(signal.SIGHUP, signal.SIG_IGN)
    status_path = Path(str(stem) + '.status.json')
    start = time.monotonic()
    status = dict(status='STARTING', started_utc=now(), supervisor_pid=os.getpid(),
                  seconds_limit=args.seconds, command=[args.solver, '--sat', '-t',
                  str(args.seconds), '-w', str(stem) + '.sol', str(stem) + '.cnf'])
    write_status(status_path, status)
    try:
        with open(str(stem) + '-solve.log', 'wb') as output:
            child = subprocess.Popen(status['command'], stdin=subprocess.DEVNULL,
                stdout=output, stderr=subprocess.STDOUT, start_new_session=True,
                close_fds=True)
            status.update(status='RUNNING', solver_pid=child.pid)
            write_status(status_path, status)
            try:
                code = child.wait(timeout=args.seconds + 60)
            except subprocess.TimeoutExpired:
                child.terminate()
                code = child.wait(timeout=30)
                status['supervisor_timeout'] = True
        status.update(returncode=code, finished_utc=now(), wall_seconds=time.monotonic() - start,
            status={10: 'SAT', 20: 'UNSAT', 0: 'TIMEOUT_OR_UNKNOWN'}.get(code, 'INTERRUPTED'))
    except Exception as error:
        status.update(status='SUPERVISOR_ERROR', error=type(error).__name__ + ': ' + str(error),
                      finished_utc=now(), wall_seconds=time.monotonic() - start)
    write_status(status_path, status)
