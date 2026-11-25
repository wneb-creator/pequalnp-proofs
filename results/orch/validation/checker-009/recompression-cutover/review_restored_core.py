import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import sys

parser = argparse.ArgumentParser()
parser.add_argument('--config', required=True)
parser.add_argument('--config-sha256', required=True)
args = parser.parse_args()
raw = Path(args.config).read_bytes()
assert hashlib.sha256(raw).hexdigest() == args.config_sha256
config = json.loads(raw)
journal = Path(config['state_dir']) / 'transaction.json'
plan = json.loads(journal.read_text())
assert plan['status'] == 'restored'
errors = []
checked = size = 0
for row in plan['files']:
    path = Path(row['path'])
    try:
        assert path.is_symlink() and os.readlink(path) == row['target']
        before = path.stat()
        assert (before.st_dev, before.st_ino, before.st_size) == (row['fd_dev'], row['fd_ino'], row['size'])
        assert (stat.S_IMODE(before.st_mode), before.st_mtime_ns) == (row['mode'], row['mtime_ns'])
        link = path.lstat()
        assert (link.st_mtime_ns, stat.S_IMODE(link.st_mode)) == (row['symlink_mtime_ns'], row['symlink_mode'])
        value = hashlib.sha256()
        with path.open('rb') as stream:
            for data in iter(lambda: stream.read(1048576), b''):
                value.update(data)
        assert value.hexdigest() == row['sha256']
        after = path.stat()
        assert (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) == (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
        checked += 1
        size += row['size']
    except Exception as error:
        errors.append({'path': str(path), 'error': str(error) or type(error).__name__})
print(json.dumps({'status': 'PASS' if not errors else 'FAIL', 'files': checked,
                  'bytes': size, 'journal': str(journal),
                  'config_sha256': args.config_sha256, 'errors': errors}, sort_keys=True))
sys.exit(0 if not errors else 1)
