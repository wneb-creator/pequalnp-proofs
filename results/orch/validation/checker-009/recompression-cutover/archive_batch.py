import argparse
import fcntl
import gzip
import hashlib
import json
import os
import stat
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-45')


def digest(stream):
    result = hashlib.sha256()
    size = 0
    for block in iter(lambda: stream.read(1024 * 1024), b''):
        result.update(block)
        size += len(block)
    return size, result.hexdigest()


def sync_dir(path):
    fd = os.open(path, os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def archive(row, record_dir):
    source = Path(row['path'])
    if not source.is_absolute() or not source.is_relative_to(BASE) or '..' in source.parts:
        raise RuntimeError('source outside scratch')
    if any(p.is_symlink() for p in (source, *source.parents)):
        raise RuntimeError('source or ancestor is a symlink')
    target = source.with_name(source.name + '.gz')
    record = record_dir / (hashlib.sha256(str(source).encode()).hexdigest() + '.json')
    if not source.exists():
        if not record.is_file() or record.is_symlink() or not target.is_file() or target.is_symlink():
            raise RuntimeError('missing source has no durable recovery record')
        saved = json.loads(record.read_text())
        if any(saved.get(key) != value for key, value in row.items()) or saved['archive'] != str(target):
            raise RuntimeError('retired source recovery record differs')
        with target.open('rb') as stream:
            if digest(stream) != (saved['archive_bytes'], saved['archive_sha256']):
                raise RuntimeError('retired source archive differs')
        with gzip.open(target, 'rb') as stream:
            if digest(stream) != (row['identity']['size'], row['sha256']):
                raise RuntimeError('retired source roundtrip differs')
        return saved
    before = source.stat()
    expected = {'dev': before.st_dev, 'ino': before.st_ino, 'size': before.st_size,
                'mode': stat.S_IMODE(before.st_mode), 'mtime_ns': before.st_mtime_ns}
    if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1 or expected != row['identity']:
        raise RuntimeError('source identity changed')
    with source.open('rb') as stream:
        if digest(stream) != (row['identity']['size'], row['sha256']):
            raise RuntimeError('source pin mismatch')
    if not target.exists():
        with target.open('xb') as output:
            with gzip.GzipFile(filename='', mode='wb', fileobj=output, mtime=0) as compressed, source.open('rb') as stream:
                for block in iter(lambda: stream.read(1024 * 1024), b''):
                    compressed.write(block)
            output.flush()
            os.fsync(output.fileno())
        sync_dir(target.parent)
    if target.is_symlink() or not target.is_file():
        raise RuntimeError('unexpected archive path')
    with gzip.open(target, 'rb') as stream:
        if digest(stream) != (row['identity']['size'], row['sha256']):
            raise RuntimeError('archive roundtrip mismatch')
    with target.open('rb') as stream:
        size, sha = digest(stream)
    data = dict(row, archive=str(target), archive_bytes=size, archive_sha256=sha,
                recovery='gzip-decompress archive to source; verify source SHA256/size; restore identity.mode and identity.mtime_ns')
    encoded = (json.dumps(data, indent=2) + '\n').encode()
    if record.exists():
        if record.is_symlink() or record.read_bytes() != encoded:
            raise RuntimeError('historical record differs')
    else:
        with record.open('xb') as output:
            output.write(encoded)
            output.flush()
            os.fsync(output.fileno())
        sync_dir(record.parent)
    after = source.stat()
    if (before.st_dev, before.st_ino, before.st_size, before.st_mode, before.st_mtime_ns) != (
            after.st_dev, after.st_ino, after.st_size, after.st_mode, after.st_mtime_ns):
        raise RuntimeError('source changed before retirement')
    with source.open('rb') as stream:
        if digest(stream) != (row['identity']['size'], row['sha256']):
            raise RuntimeError('source bytes changed before retirement')
    source.unlink()
    sync_dir(source.parent)
    return data


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--plan', required=True)
    parser.add_argument('--plan-sha256', required=True)
    parser.add_argument('--records', required=True)
    args = parser.parse_args()
    plan = Path(args.plan)
    data = plan.read_bytes()
    if hashlib.sha256(data).hexdigest() != args.plan_sha256:
        raise RuntimeError('unreviewed archive plan')
    rows = json.loads(data)
    if len({row['path'] for row in rows}) != len(rows):
        raise RuntimeError('duplicate planned source')
    records = Path(args.records)
    if not records.is_absolute() or not records.is_relative_to(BASE):
        raise RuntimeError('record directory outside scratch')
    records.mkdir(parents=True, exist_ok=True)
    sync_dir(records.parent)
    with (BASE / 'resource-wrapper/storage-state/phase.lock').open('r+') as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        result = [archive(row, records) for row in rows]
    print(json.dumps({'status': 'PASS', 'files': len(result),
                      'raw_bytes': sum(row['identity']['size'] for row in result),
                      'compressed_bytes': sum(row['archive_bytes'] for row in result),
                      'records': str(records)}), flush=True)


if __name__ == '__main__':
    main()
