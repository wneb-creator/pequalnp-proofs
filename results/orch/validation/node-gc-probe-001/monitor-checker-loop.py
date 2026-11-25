import datetime
import json
import os
import re
import sys
import time
from pathlib import Path

assert len(sys.argv) in (2, 3) and re.fullmatch(r'(checker|fallback-smoke)-[0-9]{3}', sys.argv[1])
label = sys.argv[1]
base = Path('/tmp/oec/pequalnp-pilot-45')
base_journal = Path(sys.argv[2]) if len(sys.argv) == 3 else base / 'resource-wrapper/storage-state/transaction.json'
assert base_journal.is_relative_to(base) and base_journal.name == 'transaction.json'

def phase(path):
    try:
        with path.open('rb') as f:
            first = f.read(128)
            f.seek(max(0, os.fstat(f.fileno()).st_size - 256))
            match = re.search(br'"status"\s*:\s*"([^"]+)"', first + f.read(256))
        return match.group(1).decode('ascii') if match else 'unknown'
    except FileNotFoundError:
        return 'no_active_journal'

while True:
    cg = Path('/sys/fs/cgroup')
    stat = dict(line.split() for line in (cg / 'memory.stat').read_text().splitlines())
    row = {
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'memory_current': int((cg / 'memory.current').read_text()),
        'memory_events': (cg / 'memory.events').read_text().strip(),
        'memory_stat': {k: int(stat[k]) for k in ('anon', 'file', 'shmem', 'file_mapped', 'inactive_file', 'active_file')},
        'disk_free': os.statvfs(base).f_bavail * os.statvfs(base).f_frsize,
        'base_phase': phase(base_journal),
        'core_phase': phase(base / 'core-phase/state/transaction.json'),
        'finished': (base / (label + '.exit')).exists(),
    }
    pid_file = base / (label + '.pid')
    if pid_file.exists():
        pid_text = pid_file.read_text().strip()
        if pid_text.isdecimal():
            row['node_pid'] = int(pid_text)
            try:
                status = Path('/proc', pid_text, 'status').read_text()
                row['node_memory_kib'] = {
                    key: int(value)
                    for key, value in re.findall(
                        r'^(VmRSS|RssAnon|RssFile|RssShmem):\s+(\d+)\s+kB$',
                        status, re.MULTILINE)
                }
            except FileNotFoundError:
                row['node_memory_kib'] = None
    with (base / (label + '-resources.jsonl')).open('a') as f:
        f.write(json.dumps(row) + '\n')
    if row['finished']:
        break
    time.sleep(5)
