import hashlib
import json
import os
from pathlib import Path
import stat
import sys

BASE = Path('/tmp/oec/pequalnp-pilot-45/core-phase')
plan = json.loads((BASE / 'state/transaction.json').read_text())
if plan.get('status') != 'restored':
    raise RuntimeError('independent core audit requires a restored transaction')
errors = []
checked = 0
size = 0
for row in plan['files']:
    path = Path(row['path'])
    try:
        if not path.is_symlink() or os.readlink(path) != row['target']:
            raise RuntimeError('original FD symlink not restored')
        current = path.stat()
        if (current.st_dev, current.st_ino, current.st_size) != (
                row['fd_dev'], row['fd_ino'], row['size']):
            raise RuntimeError('FD identity or size mismatch')
        if stat.S_IMODE(current.st_mode) != row['mode'] or current.st_mtime_ns != row['mtime_ns']:
            raise RuntimeError('target metadata mismatch')
        link = path.lstat()
        if link.st_mtime_ns != row['symlink_mtime_ns']:
            raise RuntimeError('symlink mtime mismatch')
        if stat.S_IMODE(link.st_mode) != row['symlink_mode']:
            raise RuntimeError('symlink mode mismatch')
        value = hashlib.sha256()
        with path.open('rb') as stream:
            for data in iter(lambda: stream.read(1024 * 1024), b''):
                value.update(data)
        if value.hexdigest() != row['sha256']:
            raise RuntimeError('SHA256 mismatch')
        checked += 1
        size += current.st_size
    except Exception as error:
        errors.append({'path': str(path), 'error': str(error)})
print(json.dumps({'status': 'PASS' if not errors else 'FAIL', 'files': checked,
                  'bytes': size, 'errors': errors}, sort_keys=True))
sys.exit(0 if not errors else 1)
