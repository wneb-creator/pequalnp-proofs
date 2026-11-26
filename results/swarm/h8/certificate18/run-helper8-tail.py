from pathlib import Path
import datetime, hashlib, json, os, subprocess, time

ROOT = Path('/tmp/oec/pnp-swarm-2373-8/cert18')
LOGS = ROOT / 'helper8-tail-logs'
LOGS.mkdir(exist_ok=True)
REPORT = ROOT / 'helper8-tail-report.json'
report = {'range': [4352, 4608], 'interval': 'half-open',
          'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'status': 'running', 'builds': [], 'running': []}

def save():
    temporary = REPORT.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(report, indent=2) + '\n')
    temporary.replace(REPORT)

def batch(names, limit):
    pending = {}
    for name in names:
        source = ROOT / f'{name}.lean'
        out = (LOGS / f'{name}.stdout').open('w')
        err = (LOGS / f'{name}.stderr').open('w')
        started = time.monotonic()
        process = subprocess.Popen(['python3', '/tmp/oec/pnp-swarm-2373-8/lean-run.py',
            '-M', str(limit), '--profile', '-R', str(ROOT),
            '-o', str(ROOT / f'{name}.olean'), str(source)], stdout=out, stderr=err)
        entry = {'module': name, 'pid': process.pid,
                 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
        pending[process.pid] = (process, entry, started, out, err)
        report['running'].append(entry.copy())
        save()
    failures = []
    while pending:
        pid, status, usage = os.wait4(-1, 0)
        process, entry, started, out, err = pending.pop(pid)
        process.returncode = os.waitstatus_to_exitcode(status)
        out.close(); err.close()
        entry.update(returncode=process.returncode, wall_seconds=time.monotonic()-started,
                     maxrss_KiB=usage.ru_maxrss, user_seconds=usage.ru_utime,
                     system_seconds=usage.ru_stime)
        report['running'] = [v for v in report['running'] if v['pid'] != pid]
        report['builds'].append(entry)
        if process.returncode:
            failures.append(entry)
        save()
        print(json.dumps(entry), flush=True)
    if failures:
        report['status'] = 'failed'
        save()
        raise SystemExit(1)

save()
batch(['H8Tail4352', 'H8Tail4480'], 5500)
batch(['H8TailRange'], 4500)
batch(['H8TailAxioms'], 4500)
report['status'] = 'all_builds_passed'
report['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
save()
