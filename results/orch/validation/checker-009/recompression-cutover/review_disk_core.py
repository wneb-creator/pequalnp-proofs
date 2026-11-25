import fcntl
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess

BASE = Path('/tmp/oec/pequalnp-pilot-45')
HERE = BASE / 'recompression-cutover'
STAGE = BASE / 'core-phase/disk-state-001'

def sha(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for data in iter(lambda: stream.read(1048576), b''):
            value.update(data)
    return value.hexdigest()

report = json.loads((STAGE / 'ready.json').read_text())
assert report['status'] == 'staged_only'
for name in ('pack', 'prepared', 'source_pack', 'source_prepared'):
    assert sha(report[name]) == report[name + '_sha256']
before = json.loads(Path(report['source_prepared']).read_text())
after = json.loads(Path(report['prepared']).read_text())
assert {k: v for k, v in before.items() if k != 'files'} == {k: v for k, v in after.items() if k != 'files'}
assert len(before['files']) == len(after['files']) == 2322
strip = lambda row: {key: value for key, value in row.items() if key not in ('offset', 'compressed')}
assert [strip(row) for row in before['files']] == [strip(row) for row in after['files']]
with open(report['source_pack'], 'rb') as stream:
    info = os.fstat(stream.fileno())
    assert (info.st_dev, info.st_ino, info.st_size) == (1, 24087, report['source_bytes'])
    assert fcntl.fcntl(stream.fileno(), fcntl.F_GET_SEALS) == 15
pack = Path(report['pack'])
assert not pack.is_symlink() and stat.S_IMODE(pack.stat().st_mode) == 0o400
assert pack.stat().st_size == report['pack_bytes']
count = raw_bytes = offset = 0
with (HERE / 'review-disk-core-decoder.stderr').open('wb') as error:
    process = subprocess.Popen(['zstd', '-d', '-c', str(pack)], stdout=subprocess.PIPE, stderr=error)
    try:
        for row in after['files']:
            assert row['offset'] == offset
            offset += row['compressed']
            remaining = row['size']
            digest = hashlib.sha256()
            while remaining:
                data = process.stdout.read(min(remaining, 1048576))
                assert data, 'short independent decoder output'
                remaining -= len(data)
                digest.update(data)
            assert digest.hexdigest() == row['sha256']
            path = Path(row['path'])
            assert path.is_symlink() and os.readlink(path) == row['target']
            current = path.stat()
            assert (current.st_dev, current.st_ino, current.st_size, stat.S_IMODE(current.st_mode), current.st_mtime_ns) == (row['fd_dev'], row['fd_ino'], row['size'], row['mode'], row['mtime_ns'])
            link = path.lstat()
            assert (link.st_mtime_ns, stat.S_IMODE(link.st_mode)) == (row['symlink_mtime_ns'], row['symlink_mode'])
            assert sha(path) == row['sha256']
            count += 1
            raw_bytes += row['size']
        assert process.stdout.read(1) == b''
    finally:
        process.stdout.close()
        code = process.wait()
    assert code == 0
assert offset == report['pack_bytes'] and raw_bytes == report['raw_bytes']
assert (HERE / 'review-disk-core-decoder.stderr').stat().st_size == 0
print(json.dumps({'status': 'PASS', 'files': count, 'raw_bytes': raw_bytes,
                  'pack_bytes': report['pack_bytes'], 'pack_sha256': report['pack_sha256'],
                  'prepared_sha256': report['prepared_sha256'],
                  'source_sealed_pack': 'unchanged; full seals and inode checked',
                  'live_runtime': 'SHA, size, mode, mtime, FD identity and symlink metadata exact',
                  'independent_decoder': 'zstd CLI; complete coverage',
                  'ready_sha256': sha(STAGE / 'ready.json')}, sort_keys=True))
