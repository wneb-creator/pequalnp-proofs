#!/usr/bin/env python3
"""Run Kissat with binary DRAT through a bounded FIFO relay to dsr-trim.

No proof file is retained. Logs, an immutable CNF snapshot, hashes and resource
measurements are retained in a NEW output directory. Exit 0 means verified
CNF UNSAT; 10 means unvalidated SAT; 2 UNKNOWN; 3 aborted; 1 failure.
An external coordinator can create --abort-file on lease loss; it is never read.
"""
import argparse
from contextlib import ExitStack
import ctypes
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import select
import shutil
import signal
import subprocess
import sys
import time

CHUNK = 65536
BUFFER_LIMIT = 1048576
HEX = re.compile(r'[0-9a-f]{64}\Z')
OPTION = re.compile(r'--[a-z][a-z0-9-]*=(?:[0-9]+|true|false)\Z')
PRESETS = {'--plain', '--basic', '--default', '--sat', '--unsat'}


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(CHUNK), b''):
            h.update(block)
    return h.hexdigest()


def atomic_json(path, value):
    temp = path.with_suffix(path.suffix + '.tmp')
    with temp.open('w') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')
    os.replace(temp, path)


def verdicts(path):
    with path.open('rb') as stream:
        return [line.decode('ascii', errors='replace').strip()
                for line in stream if line.startswith(b's ')]


def child_setup(memory_mb, parent_pid):
    # The runner is single-threaded. Linux kills each direct worker if this
    # supervisor dies even by SIGKILL; orderly shutdown also kills its group.
    def setup():
        if memory_mb:
            size = memory_mb * 1024 * 1024
            resource.setrlimit(resource.RLIMIT_AS, (size, size))
        if sys.platform.startswith('linux'):
            libc = ctypes.CDLL(None, use_errno=True)
            if libc.prctl(1, signal.SIGKILL, 0, 0, 0) != 0:
                os._exit(125)
            if os.getppid() != parent_pid:
                os._exit(125)
    return setup


def sample_rss(proc):
    # Explicit worker PID only; never reads environment or command-line files.
    if proc is None:
        return 0
    try:
        with open(f'/proc/{proc.pid}/status') as stream:
            for line in stream:
                if line.startswith('VmHWM:'):
                    return int(line.split()[1])
    except (OSError, ValueError):
        pass
    return 0


def stop_workers(workers, grace):
    for proc in workers:
        if proc is not None and proc.poll() is None:
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
    deadline = time.monotonic() + grace
    while any(p is not None and p.poll() is None for p in workers) and time.monotonic() < deadline:
        time.sleep(0.02)
    for proc in workers:
        if proc is not None and proc.poll() is None:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
    for proc in workers:
        if proc is not None:
            proc.wait()


def run(args):
    start = time.monotonic()
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    out = args.output_dir.resolve()
    out.mkdir(mode=0o700)  # Refuse reuse, symlinks, or overwriting existing logs.
    stop = [None]
    old_handlers = {}
    def handler(sig, _frame):
        stop[0] = 'signal_' + signal.Signals(sig).name
    for sig in (signal.SIGINT, signal.SIGTERM):
        old_handlers[sig] = signal.signal(sig, handler)
    solver = checker = None
    fifo_fd = guard_fd = None
    fifo = out / 'proof.fifo'
    snapshot = out / 'instance.cnf'
    proof_hash = hashlib.sha256()
    proof_bytes = forwarded = records = 0
    pending = bytearray()
    eof = input_closed = broken_pipe = checker_verified_early = False
    reason = None
    peaks = {'solver': 0, 'checker': 0}
    identities = {}
    maximum_pending = 0
    log_names = ['solver.stdout.txt', 'solver.stderr.txt', 'checker.stdout.txt', 'checker.stderr.txt']
    try:
        with ExitStack() as stack:
            logs = [stack.enter_context((out / name).open('xb', buffering=0)) for name in log_names]
            shutil.copyfile(args.cnf, snapshot)
            snapshot.chmod(0o400)
            identities = {'cnf_sha256': digest(snapshot), 'solver_sha256': digest(args.solver),
                          'checker_sha256': digest(args.checker)}
            if identities['checker_sha256'] != args.checker_sha256:
                raise ValueError('checker digest does not match the expected unchanged binary')
            if args.cnf_sha256 and identities['cnf_sha256'] != args.cnf_sha256:
                raise ValueError('CNF digest does not match the expected snapshot')
            if args.abort_file and args.abort_file.exists():
                stop[0] = 'external_abort_file'
            if stop[0] is None:
                os.mkfifo(fifo, mode=0o600)
                fifo_fd = os.open(fifo, os.O_RDONLY | os.O_NONBLOCK)
                # Hold off EOF until the producer has exited, including startup
                # before Kissat opens the FIFO, and zero-byte SAT/UNKNOWN proofs.
                guard_fd = os.open(fifo, os.O_WRONLY | os.O_NONBLOCK)
                parent = os.getpid()
                checker = subprocess.Popen([str(args.checker), '--forward', str(snapshot)],
                    stdin=subprocess.PIPE, stdout=logs[2], stderr=logs[3], bufsize=0,
                    cwd=out, start_new_session=True,
                    preexec_fn=child_setup(args.checker_memory_mb, parent))
                os.set_blocking(checker.stdin.fileno(), False)
                solver = subprocess.Popen([str(args.solver), *args.solver_arg,
                    '--no-color', str(snapshot), str(fifo)], stdin=subprocess.DEVNULL,
                    stdout=logs[0], stderr=logs[1], cwd=out, start_new_session=True,
                    preexec_fn=child_setup(args.solver_memory_mb, parent))
                last_progress = last_resources = 0.0
                while stop[0] is None and reason is None:
                    now = time.monotonic()
                    if args.abort_file and args.abort_file.exists():
                        stop[0] = 'external_abort_file'
                        break
                    if now - start > args.max_seconds:
                        stop[0] = 'wall_time_limit'
                        break
                    if now - last_resources >= 0.25:
                        peaks['solver'] = max(peaks['solver'], sample_rss(solver))
                        peaks['checker'] = max(peaks['checker'], sample_rss(checker))
                        if shutil.disk_usage(out).free < args.min_free_mb * 1024 * 1024:
                            stop[0] = 'low_disk_space'
                            break
                        last_resources = now
                    solver_rc, checker_rc = solver.poll(), checker.poll()
                    if solver_rc is not None and guard_fd is not None:
                        os.close(guard_fd)
                        guard_fd = None
                    if solver_rc is not None and solver_rc not in (0, 10, 20):
                        reason = 'unexpected_solver_exit'
                        break
                    if checker_rc is not None:
                        cv = verdicts(out / 'checker.stdout.txt')
                        if checker_rc != 0:
                            reason = 'checker_failed'
                            break
                        if cv == ['s VERIFIED UNSAT']:
                            # DSR may stop at a verified empty-clause prefix.
                            # Keep hashing/draining all remaining producer bytes.
                            checker_verified_early = True
                            pending.clear()
                            if not input_closed:
                                checker.stdin.close()
                                input_closed = True
                        elif not input_closed:
                            reason = 'checker_stopped_before_proof_eof_without_UNSAT'
                            break
                    if eof and not pending and not input_closed:
                        checker.stdin.close()
                        input_closed = True
                    if solver_rc is not None and checker_rc is not None and eof:
                        break
                    reads = [fifo_fd] if not eof and len(pending) < BUFFER_LIMIT else []
                    writes = [checker.stdin.fileno()] if pending and not input_closed and not broken_pipe else []
                    ready_read, ready_write, _ = select.select(reads, writes, [], 0.05)
                    if ready_write:
                        try:
                            sent = os.write(checker.stdin.fileno(), pending)
                            del pending[:sent]
                            forwarded += sent
                        except BlockingIOError:
                            pass
                        except BrokenPipeError:
                            broken_pipe = True
                    if ready_read:
                        try:
                            block = os.read(fifo_fd, min(CHUNK, BUFFER_LIMIT - len(pending)))
                        except BlockingIOError:
                            block = None
                        if block == b'':
                            eof = True
                        elif block:
                            proof_hash.update(block)
                            proof_bytes += len(block)
                            # Canonical binary DRAT uses one zero byte per line.
                            # Conservatively limit all zero bytes, not only additions.
                            records += block.count(b'\0')
                            if records > args.max_proof_records:
                                stop[0] = 'proof_record_safety_limit'
                                break
                            if not checker_verified_early:
                                pending.extend(block)
                                maximum_pending = max(maximum_pending, len(pending))
                    if now - last_progress >= 5.0:
                        atomic_json(out / 'progress.json', {'state': 'RUNNING',
                            'solver_pid':solver.pid, 'checker_pid':checker.pid,
                            'elapsed_seconds': round(now - start, 3), 'proof_bytes_read': proof_bytes,
                            'proof_sha256_prefix': proof_hash.hexdigest(), 'proof_stream_complete': False,
                            'bytes_forwarded': forwarded, 'zero_bytes': records,
                            'sampled_peak_rss_kib': peaks, **identities})
                        last_progress = now
    except Exception as error:
        reason = 'runner_error_' + type(error).__name__
        # Controlled exception text includes paths/OS errors, never environment.
        error_detail = str(error)
    else:
        error_detail = None
    finally:
        stop_workers([solver, checker], args.kill_grace_seconds)
        if checker is not None and checker.stdin is not None and not checker.stdin.closed:
            checker.stdin.close()
        for fd in (fifo_fd, guard_fd):
            if fd is not None:
                os.close(fd)
        fifo.unlink(missing_ok=True)
        for sig, prior in old_handlers.items():
            signal.signal(sig, prior)

    solver_rc = solver.returncode if solver is not None else None
    checker_rc = checker.returncode if checker is not None else None
    sv = verdicts(out / 'solver.stdout.txt')
    cv = verdicts(out / 'checker.stdout.txt')
    if identities and snapshot.exists() and digest(snapshot) != identities['cnf_sha256']:
        reason = 'CNF_snapshot_changed'
    if identities and (digest(args.solver) != identities['solver_sha256'] or
                       digest(args.checker) != identities['checker_sha256']):
        reason = 'executable_changed'
    complete = eof and solver_rc in (0, 10, 20) and stop[0] is None and reason is None
    accepted = complete and solver_rc == 20 and sv == ['s UNSATISFIABLE'] and checker_rc == 0 and cv == ['s VERIFIED UNSAT']
    if stop[0] is not None:
        status, exit_code = 'ABORTED', 3
    elif reason is not None:
        status, exit_code = 'FAILED', 1
    elif accepted:
        status, exit_code = 'VERIFIED_UNSAT', 0
    elif complete and solver_rc == 10 and sv == ['s SATISFIABLE'] and checker_rc == 0 and cv == ['s VALID']:
        status, exit_code = 'SAT_UNVALIDATED', 10
    elif complete and solver_rc == 0 and sv in ([], ['s UNKNOWN']) and checker_rc == 0 and cv == ['s VALID']:
        status, exit_code = 'UNKNOWN', 2
    else:
        status, exit_code = 'FAILED', 1
        reason = 'solver_checker_verdict_mismatch'
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    report = {'status':status, 'accepted_CNF_UNSAT':accepted, 'reason':stop[0] or reason,
        'error_detail':error_detail, 'solver_exit':solver_rc, 'checker_exit':checker_rc,
        'solver_verdicts':sv, 'checker_verdicts':cv, 'proof_bytes_read':proof_bytes,
        'proof_sha256':proof_hash.hexdigest(), 'proof_stream_complete':complete,
        'proof_bytes_forwarded_to_checker_pipe':forwarded,
        'proof_bytes_not_forwarded':proof_bytes-forwarded,
        'checker_may_stop_after_verified_empty_clause':checker_verified_early,
        'proof_retained':False, 'zero_bytes_counted':records, 'max_pending_bytes':maximum_pending,
        'relay_buffer_limit_bytes':BUFFER_LIMIT, 'elapsed_seconds':round(time.monotonic()-start,6),
        'children_user_cpu_seconds':usage.ru_utime-usage_before.ru_utime,
        'children_system_cpu_seconds':usage.ru_stime-usage_before.ru_stime,
        'children_maxrss_kib':usage.ru_maxrss, 'sampled_peak_rss_kib':peaks,
        'runner_cpu_seconds':time.process_time(), 'solver_options':args.solver_arg,
        'limits':{'checker_address_space_mb':args.checker_memory_mb,
                  'solver_address_space_mb':args.solver_memory_mb,'max_seconds':args.max_seconds,
                  'max_proof_zero_bytes':args.max_proof_records,'min_free_mb':args.min_free_mb},
        'solver_pid':solver.pid if solver else None, 'checker_pid':checker.pid if checker else None,
        'logs':{name:{'bytes':(out/name).stat().st_size,'sha256':digest(out/name)} for name in log_names},
        'scope':'Online CNF certificate checking only; no retained replayable certificate or Lean acceptance.',
        **identities}
    atomic_json(out/'result.json', report)
    atomic_json(out/'progress.json', report)
    return report, exit_code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cnf',type=Path)
    parser.add_argument('output_dir',type=Path)
    parser.add_argument('--solver',type=Path,required=True)
    parser.add_argument('--checker',type=Path,required=True)
    parser.add_argument('--checker-sha256',required=True)
    parser.add_argument('--cnf-sha256')
    parser.add_argument('--solver-arg',action='append',default=[])
    parser.add_argument('--abort-file',type=Path)
    parser.add_argument('--max-seconds',type=float,default=3600)
    parser.add_argument('--kill-grace-seconds',type=float,default=2)
    parser.add_argument('--solver-memory-mb',type=int,default=4000)
    parser.add_argument('--checker-memory-mb',type=int,default=4000)
    parser.add_argument('--max-proof-records',type=int,default=100000000)
    parser.add_argument('--min-free-mb',type=int,default=256)
    args=parser.parse_args()
    for name in ('checker_sha256','cnf_sha256'):
        if getattr(args,name) is not None and not HEX.fullmatch(getattr(args,name)):
            parser.error(name+' must be lowercase SHA-256 hex')
    for name in ('max_seconds','kill_grace_seconds','solver_memory_mb','checker_memory_mb','max_proof_records','min_free_mb'):
        if not 0 < getattr(args,name) < float('inf'):
            parser.error(name+' must be positive and finite')
    if args.max_proof_records > 100000000:
        parser.error('default-width checker safety limit cannot exceed 100000000 proof records')
    for arg in args.solver_arg:
        if arg not in PRESETS and not OPTION.fullmatch(arg):
            parser.error('solver args must be numeric/Boolean long options or known presets')
        if arg.startswith(('--binary=', '--flushproof=')):
            parser.error('proof format/flush overrides are not accepted')
    for name in ('cnf','solver','checker'):
        setattr(args,name,getattr(args,name).resolve(strict=True))
    if args.abort_file:
        args.abort_file=args.abort_file.resolve()
    report,code=run(args)
    print(json.dumps({'status':report['status'],'accepted_CNF_UNSAT':report['accepted_CNF_UNSAT'],
                      'result':str(args.output_dir.resolve()/'result.json')}))
    return code


if __name__=='__main__':
    sys.exit(main())
