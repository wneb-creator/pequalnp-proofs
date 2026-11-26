from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import time

ROOT = Path('/tmp/oec/pnp-swarm-2373-8/cert18')
LOGS = ROOT / 'helper8-early-logs'
LOGS.mkdir(exist_ok=True)
REPORT = ROOT / 'helper8-early-report.json'
report = {'range': [256, 768], 'interval': 'half-open',
          'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'status': 'running', 'builds': [], 'running': [], 'receipts': []}

def save():
    temporary = REPORT.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(report, indent=2) + '\n')
    temporary.replace(REPORT)

def batch(names, limit):
    processes = []
    for name in names:
        source = ROOT / f'{name}.lean'
        stdout = (LOGS / f'{name}.stdout').open('w')
        stderr = (LOGS / f'{name}.stderr').open('w')
        started = time.monotonic()
        process = subprocess.Popen([
            'python3', '/tmp/oec/pnp-swarm-2373-8/lean-run.py', '-M', str(limit),
            '--profile', '-R', str(ROOT), '-o', str(ROOT / f'{name}.olean'), str(source),
        ], stdout=stdout, stderr=stderr)
        entry = {'module': name, 'pid': process.pid,
                 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
        report['running'].append(entry.copy())
        processes.append((process, entry, started, stdout, stderr))
        save()
    failures = []
    for process, entry, started, stdout, stderr in processes:
        _, status, usage = os.wait4(process.pid, 0)
        process.returncode = os.waitstatus_to_exitcode(status)
        stdout.close()
        stderr.close()
        entry.update(returncode=process.returncode, wall_seconds=time.monotonic()-started,
                     maxrss_KiB=usage.ru_maxrss, user_seconds=usage.ru_utime,
                     system_seconds=usage.ru_stime)
        report['running'] = [v for v in report['running'] if v['pid'] != process.pid]
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
batch(['H8Extra256', 'H8Extra384'], 5500)
batch(['H8ExtraRange'], 4500)
batch(['H8ExtraAxioms'], 4500)
report['receipts'].append({'range': [256, 512], 'theorem': 'Helper8Extra.checked',
                           'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()})
save()
(ROOT / 'helper8-extra256-receipt.json').write_text(json.dumps(report, indent=2) + '\n')
batch(['H8Extra512', 'H8Extra640'], 5500)
batch(['H8EarlyRange'], 4500)
batch(['H8EarlyAxioms'], 4500)
report['receipts'].append({'range': [256, 768], 'theorem': 'Helper8Extra.checked_early',
                           'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()})
report['status'] = 'all_builds_passed'
report['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
save()
