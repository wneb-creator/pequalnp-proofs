import gzip
import hashlib
import json
import os
import stat
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-45')
SOURCE = BASE / 'compressed-artifacts/editor-offloaded.jsonl'
ARCHIVE = SOURCE.with_suffix(SOURCE.suffix + '.gz')
RECORD = BASE / 'recompression-cutover/editor-offloaded-archive.json'


def sha(stream):
    h = hashlib.sha256()
    count = 0
    for block in iter(lambda: stream.read(1024 * 1024), b''):
        h.update(block)
        count += len(block)
    return count, h.hexdigest()


def sync_dir(path):
    fd = os.open(path, os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


if SOURCE.is_symlink() or not SOURCE.is_file():
    raise RuntimeError('historical source is not regular')
before = SOURCE.stat()
with SOURCE.open('rb') as stream:
    size, digest = sha(stream)
with ARCHIVE.open('xb') as output:
    with gzip.GzipFile(filename='', mode='wb', fileobj=output, mtime=0) as compressed, SOURCE.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            compressed.write(block)
    output.flush()
    os.fsync(output.fileno())
sync_dir(ARCHIVE.parent)
with gzip.open(ARCHIVE, 'rb') as stream:
    if sha(stream) != (size, digest):
        raise RuntimeError('historical archive roundtrip differs')
with ARCHIVE.open('rb') as stream:
    compressed_size, compressed_sha = sha(stream)
record = {'source': str(SOURCE), 'size': size, 'sha256': digest,
          'mode': stat.S_IMODE(before.st_mode), 'mtime_ns': before.st_mtime_ns,
          'device': before.st_dev, 'inode': before.st_ino,
          'archive': str(ARCHIVE), 'archive_bytes': compressed_size,
          'archive_sha256': compressed_sha,
          'recovery': 'gzip decompress archive to source; verify size and SHA256; restore mode and mtime_ns from this record'}
with RECORD.open('x') as output:
    json.dump(record, output, indent=2)
    output.write('\n')
    output.flush()
    os.fsync(output.fileno())
sync_dir(RECORD.parent)
after = SOURCE.stat()
if (before.st_dev, before.st_ino, before.st_size, before.st_mode, before.st_mtime_ns) != (
        after.st_dev, after.st_ino, after.st_size, after.st_mode, after.st_mtime_ns):
    raise RuntimeError('historical source metadata changed')
with SOURCE.open('rb') as stream:
    if sha(stream) != (size, digest):
        raise RuntimeError('historical source bytes changed')
SOURCE.unlink()
sync_dir(SOURCE.parent)
print(json.dumps(record), flush=True)
