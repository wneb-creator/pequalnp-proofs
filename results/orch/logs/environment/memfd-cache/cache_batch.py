from pathlib import Path
import datetime
import json
import os
import signal
import subprocess
import sys
import time

job = Path('/tmp/oec/pequalnp-pilot-144')
repo = Path('/workspace/pequalnp-proofs')
mathlib = repo / 'lean/.lake/packages/mathlib'
logs = job / 'full-cache-batches'
logs.mkdir(exist_ok=True)
source = mathlib / 'Mathlib'
built = mathlib / '.lake/build/lib/lean/Mathlib'
missing = sorted(path for path in source.rglob('*.lean')
                 if not (built / path.relative_to(source)).with_suffix('.olean').exists())
batch_size = int(sys.argv[1]) if len(sys.argv) > 1 else 50
chosen = missing[:batch_size]
modules = ['Mathlib.' + '.'.join(path.relative_to(source).with_suffix('').parts)
           for path in chosen]
if not modules:
    modules = ['Mathlib']
env = os.environ.copy()
toolbin = str(job / 'toolchain/lean-4.36.0-linux/bin')
env['PATH'] = str(repo / 'tools/bin') + ':' + toolbin + ':' + env.get('PATH', '')
env['PEQUALNP_REAL_LAKE'] = toolbin + '/lake'
env['PEQUALNP_HOME'] = str(job / 'build-home')
env['LAKE_ARTIFACT_CACHE'] = 'false'
env['MATHLIB_CACHE_DIR'] = str(job / 'mathlib-cache')
env['MATHLIB_CACHE_PARALLEL_MAX'] = '8'
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
record = dict(time=stamp, missing_before=len(missing), modules=modules)
base = logs / stamp
base.with_suffix('.json').write_text(json.dumps(record, indent=2) + '\n')
print('Batch', stamp, 'missing before', len(missing), 'roots', len(modules), flush=True)
with base.with_suffix('.log').open('wb') as log:
    process = subprocess.Popen([str(repo / 'tools/bin/lake'), 'exe', 'cache', 'get', *modules],
                               cwd=repo / 'lean', env=env, stdout=log, stderr=subprocess.STDOUT,
                               start_new_session=True)
    while process.poll() is None:
        space = os.statvfs(job)
        disk_free = space.f_bavail * space.f_frsize
        available = next(int(line.split()[1]) * 1024 for line in
                         Path('/proc/meminfo').read_text().splitlines()
                         if line.startswith('MemAvailable:'))
        if disk_free < 400 * 1024**2 or available < 1536 * 1024**2:
            record['capacity_stop'] = dict(disk_free=disk_free, ram_available=available)
            print('Capacity stop:', record['capacity_stop'], flush=True)
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            break
        time.sleep(1)
record['exit'] = process.returncode
if process.returncode == 0:
    with base.with_suffix('.clean.log').open('wb') as log:
        clean = subprocess.run([str(repo / 'tools/bin/lake'), 'exe', 'cache', 'clean!'],
                               cwd=repo / 'lean', env=env, stdout=log, stderr=subprocess.STDOUT)
    record['clean_exit'] = clean.returncode
missing_after = sum(not (built / path.relative_to(source)).with_suffix('.olean').exists()
                    for path in source.rglob('*.lean'))
record['missing_after'] = missing_after
base.with_suffix('.json').write_text(json.dumps(record, indent=2) + '\n')
print('Batch completed', record['exit'], 'missing after', missing_after, flush=True)
subprocess.run(['df', '-h', '/tmp'])
subprocess.run(['free', '-h'])
sys.exit(process.returncode)
