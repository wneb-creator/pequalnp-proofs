from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import time

ROOT = Path('/tmp/oec/pnp-swarm-2373-8/cert18')
REPORT = ROOT / 'helper8-range-report.json'
LOGS = ROOT / 'helper8-range-logs'
LOGS.mkdir(exist_ok=True)
report = {
    'range': [4608, 5230],
    'interval': 'half-open',
    'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'status': 'running',
    'builds': [],
}

def save():
    REPORT.write_text(json.dumps(report, indent=2) + '\n')

save()
names = [f'H8Chunk{lo}' for lo in range(4608, 5230, 128)] + ['H8Range', 'H8Axioms']
for name in names:
    source = ROOT / f'{name}.lean'
    started = time.monotonic()
    limit = '9000' if name.startswith('H8Chunk') else '4500'
    with (LOGS / f'{name}.stdout').open('w') as stdout, (LOGS / f'{name}.stderr').open('w') as stderr:
        process = subprocess.Popen([
            'python3', '/tmp/oec/pnp-swarm-2373-8/lean-run.py',
            '-M', limit, '--profile', '-R', str(ROOT),
            '-o', str(ROOT / f'{name}.olean'), str(source),
        ], stdout=stdout, stderr=stderr)
        _, status, usage = os.wait4(process.pid, 0)
        process.returncode = os.waitstatus_to_exitcode(status)
    entry = {
        'module': name,
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'returncode': process.returncode,
        'wall_seconds': time.monotonic() - started,
        'maxrss_KiB': usage.ru_maxrss,
        'user_seconds': usage.ru_utime,
        'system_seconds': usage.ru_stime,
    }
    report['builds'].append(entry)
    save()
    print(json.dumps(entry), flush=True)
    if process.returncode:
        report['status'] = 'failed'
        save()
        raise SystemExit(process.returncode)
report['status'] = 'all_builds_passed'
report['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
save()
