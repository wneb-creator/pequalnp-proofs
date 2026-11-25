from pathlib import Path
import datetime
import hashlib
import json
import os
import resource
import subprocess
import time

out = Path('/tmp/oec/pequalnp-pilot-87/weak15-mono19-v3-continuation')
binary = out / 'copy_search_weak15'
source = out / 'copy_search_weak15.cpp'
matrix = out / 'rectangles-v3.txt'
memo = out / 'input-weak15.memo'
command = [str(binary), '--cap', '19', '--first', 'oredge', '--mono-nine15',
           '--seconds', '600', '--nodes', '5000000', '--extra-rectangles', str(matrix),
           '--memo-in', str(memo), '--memo-out', str(out / 'completed-weak15.memo'),
           '--rect-trace', str(out / 'rectangles.jsonl'),
           '--bank-trace', str(out / 'banks.jsonl')]
cpu = max(os.sched_getaffinity(0))
def limits():
    resource.setrlimit(resource.RLIMIT_AS, (1_000_000_000, 1_000_000_000))
    resource.setrlimit(resource.RLIMIT_CPU, (615, 620))
    os.sched_setaffinity(0, {cpu})
    os.nice(10)

utc = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
sha = lambda p: hashlib.file_digest(p.open('rb'), 'sha256').hexdigest()
metadata = {'command': command, 'source_sha256': sha(source), 'binary_sha256': sha(binary),
            'matrix_sha256': sha(matrix), 'input_memo_sha256': sha(memo),
            'started_utc': utc(), 'cpu': cpu,
            'address_space_limit_bytes': 1_000_000_000, 'internal_estimate_limit_bytes': 800_000_000,
            'memo_input': str(memo), 'mono_nine_bound': 15, 'wall_limit_seconds': 630,
            'lineage_file': 'lineage.json'}
(out / 'run-metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
start = time.monotonic()
with (out / 'stdout.txt').open('wb') as stdout, (out / 'stderr.txt').open('wb') as stderr:
    proc = subprocess.Popen(command, cwd=out, stdout=stdout, stderr=stderr, preexec_fn=limits)
    try:
        code = proc.wait(timeout=630)
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
