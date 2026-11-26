from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import signal
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument('--threads', type=int, choices=[1, 4], required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parent
source = root / 'ThreadBench.lean'
cgroup = Path('/sys/fs/cgroup')
label = 'j' + str(args.threads)

def memory():
    stats = dict(line.split() for line in (cgroup / 'memory.stat').read_text().splitlines())
    return {
        'current': int((cgroup / 'memory.current').read_text()),
        'limit': int((cgroup / 'memory.max').read_text()),
        'anon': int(stats['anon']),
        'file': int(stats['file']),
        'kernel': int(stats['kernel']),
        'memory_events': (cgroup / 'memory.events').read_text().strip(),
    }

before = memory()
if before['current'] > 13 * (1 << 30) or before['anon'] + before['kernel'] > 8 * (1 << 30):
    raise SystemExit('Insufficient current memory headroom; no proof process started')

command = [
    'python3', '/tmp/oec/pnp-swarm-2373-8/lean-run.py',
    '-j' + str(args.threads), '-M7500', '--profile', str(source),
]
processes = subprocess.run(
    ['ps', '-C', 'lean', '-o', 'pid=,rss=,etimes=,comm='],
    capture_output=True, text=True,
).stdout
started = time.monotonic()
started_utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
samples = []
stopped_for_memory = False
with (root / (label + '.stdout')).open('w') as stdout, (root / (label + '.stderr')).open('w') as stderr:
    process = subprocess.Popen(command, cwd=root, stdout=stdout, stderr=stderr)
    while True:
        pid, status, usage = os.wait4(process.pid, os.WNOHANG)
        if pid:
            process.returncode = os.waitstatus_to_exitcode(status)
            break
        sample = memory()
        sample['seconds'] = time.monotonic() - started
        samples.append(sample)
        if sample['current'] > sample['limit'] - (1 << 30) and not stopped_for_memory:
            os.kill(process.pid, signal.SIGTERM)
            stopped_for_memory = True
        time.sleep(0.25)

report = {
    'threads': args.threads,
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'packed_direct_sha256': hashlib.sha256(Path('/tmp/oec/pnp-swarm-2373-8/cert18/PackedDirect.lean').read_bytes()).hexdigest(),
    'command': command,
    'started_utc': started_utc,
    'wall_seconds': time.monotonic() - started,
    'user_seconds': usage.ru_utime,
    'system_seconds': usage.ru_stime,
    'peak_rss_KiB': usage.ru_maxrss,
    'exit_code': process.returncode,
    'stopped_for_memory': stopped_for_memory,
    'memory_before': before,
    'memory_after': memory(),
    'peak_sampled_cgroup_bytes': max(s['current'] for s in samples),
    'cpu_quota': (cgroup / 'cpu.max').read_text().strip(),
    'other_lean_processes_before': processes,
    'output_artifacts': 'None; no -o was supplied. Proofs checked in a fresh process.',
}
(root / (label + '.memory.json')).write_text(json.dumps(samples, indent=2) + '\n')
(root / (label + '.metrics.json')).write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2), flush=True)
raise SystemExit(process.returncode)
