import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import sys
import time

parser = argparse.ArgumentParser()
parser.add_argument('--config', required=True)
parser.add_argument('--config-sha256', required=True)
args = parser.parse_args()
config_path = Path(args.config)
raw_config = config_path.read_bytes()
assert hashlib.sha256(raw_config).hexdigest() == args.config_sha256
config = json.loads(raw_config)
journal = Path(config['state_dir']) / 'transaction.json'
plan = json.loads(journal.read_text())
assert plan['status'] == 'restored'
library_pins = {row['path']: row for row in config['shared_library_whitelist']}
core_pins = {row['path']: row for row in config['retained_core_whitelist']}
assert set(library_pins).issubset({row['path'] for row in plan['build']})
started = time.monotonic()
errors = []
checked = logical_bytes = retained_core_checked = 0

for kind in ('build', 'ram'):
    for row in plan[kind]:
        path = Path(row['path'])
        try:
            pin = (library_pins if kind == 'build' else core_pins).get(str(path))
            if pin is not None:
                for key in ('size', 'sha256', 'mode', 'mtime_ns'):
                    assert row[key] == pin[key]
            if kind == 'build':
                assert not path.is_symlink() and path.is_file()
            else:
                assert path.is_symlink() and os.readlink(path) == row['target']
            before = path.stat()
            assert (before.st_size, stat.S_IMODE(before.st_mode), before.st_mtime_ns) == (row['size'], row['mode'], row['mtime_ns'])
            if kind == 'ram':
                assert (before.st_dev, before.st_ino) == (row['fd_dev'], row['fd_ino'])
                if pin is not None:
                    for key in ('pid', 'fd', 'target', 'fd_dev', 'fd_ino'):
                        assert row[key] == pin[key]
                    assert row['symlink_mtime_ns'] == pin['symlink_mtime_ns']
                    assert path.lstat().st_mtime_ns == pin['symlink_mtime_ns']
                    retained_core_checked += 1
            digest = hashlib.sha256()
            with path.open('rb') as stream:
                for block in iter(lambda: stream.read(1048576), b''):
                    digest.update(block)
            assert digest.hexdigest() == row['sha256']
            after = path.stat()
            assert (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) == (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
            checked += 1
            logical_bytes += before.st_size
        except Exception as error:
            errors.append({'path': str(path), 'error': str(error) or type(error).__name__})

print(json.dumps({'status': 'PASS' if not errors else 'FAIL', 'config_sha256': args.config_sha256,
                  'journal': str(journal), 'files_checked': checked, 'logical_bytes': logical_bytes,
                  'build_files': len(plan['build']), 'ram_files': len(plan['ram']),
                  'shared_libraries_checked': len(library_pins),
                  'retained_core_files_checked': retained_core_checked,
                  'seconds': round(time.monotonic() - started, 3), 'errors': errors}, sort_keys=True))
sys.exit(0 if not errors else 1)
