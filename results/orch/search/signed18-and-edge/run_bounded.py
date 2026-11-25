from pathlib import Path
import datetime
import hashlib
import json
import os
import resource
import subprocess
import time

root = Path('/tmp/oec/pequalnp-pilot-87')
out = root / 'signed18-search'
binary = root / 'library_route/live_search_resume'
source = root / 'library_route/live_search_resume.cpp'
trace = out / 'andedge-trace.jsonl'
command = [str(binary), '--signed', '--cap', '18', '--first', 'andedge',
           '--seconds', '300', '--nodes', '5000000', '--trace', str(trace)]
cpu = max(os.sched_getaffinity(0))
def limits():
    resource.setrlimit(resource.RLIMIT_AS, (1_000_000_000, 1_000_000_000))
    resource.setrlimit(resource.RLIMIT_CPU, (315, 320))
    os.sched_setaffinity(0, {cpu})
    os.nice(10)

utc = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
metadata = {'command': command, 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
            'binary_sha256': hashlib.sha256(binary.read_bytes()).hexdigest(),
            'started_utc': utc(), 'cpu': cpu, 'address_space_limit_bytes': 1_000_000_000,
            'resume_cache': None, 'wall_limit_seconds': 330}
(out / 'run-metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
start = time.monotonic()
with (out / 'stdout.txt').open('wb') as stdout, (out / 'stderr.txt').open('wb') as stderr:
    proc = subprocess.Popen(command, cwd=root / 'library_route', stdout=stdout,
                            stderr=stderr, preexec_fn=limits)
    try:
        code = proc.wait(timeout=330)
        metadata['external_wall_limit'] = False
    except subprocess.TimeoutExpired:
        metadata['external_wall_limit'] = True
        proc.terminate()
        try:
            code = proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()
            code = proc.wait()
metadata.update({'ended_utc': utc(), 'wall_seconds': time.monotonic() - start,
                 'exit_code': code,
                 'max_rss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss})
(out / 'run-metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
print(json.dumps(metadata))
