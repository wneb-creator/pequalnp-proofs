"""Lossless outer archive of exactly seven completed compressed journals."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys

TASK = Path('/tmp/oec/pequalnp-pilot-45')
LABELS = ('metadata-smoke', 'checker004', 'combined-smoke001', 'checker005',
          'diagnostic001', 'checker006', 'checker007')
NAMES = tuple(f'transaction-{label}.json.zst' for label in LABELS)


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def bounded(path):
    p = Path(path)
    if not p.is_absolute() or str(p) != os.path.abspath(p) or not p.is_relative_to(TASK):
        raise RuntimeError('path must be normalized and inside task scratch')
    return p


def syncdir(path):
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def atomic_json(path, value):
    temporary = path.with_name(path.name + '.new')
    if temporary.exists() or temporary.is_symlink():
        st = temporary.lstat()
        if not stat.S_ISREG(st.st_mode) or st.st_uid != os.geteuid() or st.st_nlink != 1:
            raise RuntimeError('unsafe archive metadata temporary')
        temporary.unlink()
    with temporary.open('x') as out:
        json.dump(value, out, indent=2)
        out.write('\n')
        out.flush()
        os.fsync(out.fileno())
    os.replace(temporary, path)
    syncdir(path.parent)


def check_regular(path):
    st = path.lstat()
    if not stat.S_ISREG(st.st_mode):
        raise RuntimeError('expected regular archive or sidecar')
    return st


def snapshot_sources(source):
    rows, offset = [], 0
    for name in NAMES:
        path = source / name
        sidecar = path.with_name(name + '.metadata.json')
        st = check_regular(path)
        check_regular(sidecar)
        metadata = json.loads(sidecar.read_text())
        if metadata['status'] != 'restored' or metadata['archive'] != str(path):
            raise RuntimeError('source is not the named completed journal')
        h = digest(path)
        if h != metadata['archive_sha256'] or st.st_size != metadata['archive_bytes']:
            raise RuntimeError('source compressed bytes differ from original metadata')
        rows.append({'name': name, 'offset': offset, 'length': st.st_size, 'sha256': h,
                     'mode': stat.S_IMODE(st.st_mode), 'mtime_ns': st.st_mtime_ns,
                     'device': st.st_dev, 'inode': st.st_ino,
                     'sidecar_sha256': digest(sidecar),
                     'logical_bytes': metadata['uncompressed_bytes'], 'logical_sha256': metadata['sha256']})
        offset += st.st_size
    return rows, offset


def source_matches(source, row):
    p = source / row['name']
    st = check_regular(p)
    if (st.st_size, stat.S_IMODE(st.st_mode), st.st_mtime_ns) != (row['length'], row['mode'], row['mtime_ns']):
        raise RuntimeError('source compressed archive metadata changed')
    if digest(p) != row['sha256']:
        raise RuntimeError('source compressed archive bytes changed')


def create(source, directory):
    source, directory = bounded(source), bounded(directory)
    directory.mkdir(parents=True, exist_ok=True)
    archive = directory / 'completed-journals.outer.zst'
    index = directory / 'completed-journals.index.json'
    temporary = archive.with_name(archive.name + '.partial')
    if any(p.exists() or p.is_symlink() for p in (archive, index, temporary)):
        raise RuntimeError('archive output already exists; inspect it first')
    rows, total = snapshot_sources(source)
    # Worst case grows no larger than the original stream plus zstd overhead.
    available = os.statvfs(directory).f_bavail * os.statvfs(directory).f_frsize
    if available < total + 16 * 1024 * 1024:
        raise RuntimeError('insufficient conservative archive staging headroom')
    with temporary.open('xb') as out, (directory / 'create.stderr').open('xb') as err:
        proc = subprocess.Popen(['zstd', '-q', '-c', '--long=27', '--single-thread', '-3'],
                                stdin=subprocess.PIPE, stdout=out, stderr=err)
        try:
            for row in rows:
                p = source / row['name']
                h = hashlib.sha256()
                with p.open('rb') as stream:
                    for chunk in iter(lambda: stream.read(1048576), b''):
                        h.update(chunk)
                        proc.stdin.write(chunk)
                if h.hexdigest() != row['sha256']:
                    raise RuntimeError('source changed while archiving')
            proc.stdin.close()
            if proc.wait() != 0:
                raise RuntimeError('outer compression failed')
            out.flush()
            os.fsync(out.fileno())
        except BaseException:
            if proc.poll() is None:
                proc.terminate()
                proc.wait()
            raise
    for row in rows:
        source_matches(source, row)
    os.replace(temporary, archive)
    syncdir(directory)
    record = {'format': 1, 'source_directory': str(source), 'archive_name': archive.name,
              'archive_bytes': archive.stat().st_size, 'archive_sha256': digest(archive),
              'stream_bytes': total, 'files': rows,
              'codec': ['zstd', '--long=27', '--single-thread', '-3'],
              'source_files_preserved_at_creation': True}
    atomic_json(index, record)
    verify(index, digest(index))
    return {'index': str(index), 'index_sha256': digest(index),
            'archive_bytes': record['archive_bytes'], 'saved_bytes': total - record['archive_bytes']}


def load(index, expected):
    index = bounded(index)
    check_regular(index)
    if digest(index) != expected:
        raise RuntimeError('reviewed archive index changed')
    data = json.loads(index.read_text())
    source = bounded(data['source_directory'])
    if data['format'] != 1 or data['archive_name'] != 'completed-journals.outer.zst':
        raise RuntimeError('unsupported archive index')
    if tuple(row['name'] for row in data['files']) != NAMES:
        raise RuntimeError('index does not name exactly the seven completed journals')
    offset = 0
    for row in data['files']:
        if row['offset'] != offset or row['length'] <= 0:
            raise RuntimeError('invalid indexed byte boundaries')
        offset += row['length']
        sidecar = source / (row['name'] + '.metadata.json')
        check_regular(sidecar)
        if digest(sidecar) != row['sidecar_sha256']:
            raise RuntimeError('original provenance sidecar changed')
    if offset != data['stream_bytes']:
        raise RuntimeError('indexed stream length differs')
    archive = index.parent / data['archive_name']
    if check_regular(archive).st_size != data['archive_bytes'] or digest(archive) != data['archive_sha256']:
        raise RuntimeError('outer archive bytes changed')
    return data, source, archive


def decode(data, archive, consume=None):
    with (archive.parent / 'verify.stderr').open('ab') as err:
        proc = subprocess.Popen(['zstd', '-q', '-d', '-c', str(archive)], stdout=subprocess.PIPE, stderr=err)
        try:
            for row in data['files']:
                h = hashlib.sha256()
                remaining = row['length']
                while remaining:
                    chunk = proc.stdout.read(min(1048576, remaining))
                    if not chunk:
                        raise RuntimeError('outer archive has a short member')
                    h.update(chunk)
                    remaining -= len(chunk)
                    if consume is not None:
                        consume(row, chunk)
                if h.hexdigest() != row['sha256']:
                    raise RuntimeError('reconstructed original compressed bytes differ')
            if proc.stdout.read(1) or proc.wait() != 0:
                raise RuntimeError('outer archive has trailing bytes or decoder failure')
        finally:
            if proc.poll() is None:
                proc.terminate()
                proc.wait()


def verify(index, expected):
    data, source, archive = load(index, expected)
    decode(data, archive)
    return {'verified_files': len(data['files']), 'verified_original_compressed_bytes': data['stream_bytes'],
            'index_sha256': expected}


def retire(index, expected):
    data, source, archive = load(index, expected)
    decode(data, archive)
    journal = index.parent / 'retirement.json'
    if journal.exists():
        plan = json.loads(journal.read_text())
        if plan['index_sha256'] != expected:
            raise RuntimeError('retirement journal belongs to another index')
    else:
        for row in data['files']:
            source_matches(source, row)
        plan = {'status': 'planned', 'index_sha256': expected, 'retired': []}
        atomic_json(journal, plan)
    for row in data['files']:
        p = source / row['name']
        if p.exists() or p.is_symlink():
            source_matches(source, row)
            p.unlink()
            syncdir(source)
        if row['name'] not in plan['retired']:
            plan['retired'].append(row['name'])
            atomic_json(journal, plan)
    plan['status'] = 'complete'
    atomic_json(journal, plan)
    return {'retired_files': len(plan['retired']), 'index_sha256': expected}


def restore(index, expected, output):
    data, _, archive = load(index, expected)
    output = bounded(output)
    output.mkdir(parents=True, exist_ok=True)
    for row in data['files']:
        path = output / row['name']
        if path.exists() or path.is_symlink() or path.with_name(path.name + '.outer-restore').exists():
            raise RuntimeError('restore destination already exists')
    active = {}
    def consume(row, chunk):
        name = row['name']
        if name not in active:
            path = output / (name + '.outer-restore')
            active[name] = (path, path.open('xb'))
        active[name][1].write(chunk)
    try:
        decode(data, archive, consume)
        for row in data['files']:
            temporary, stream = active[row['name']]
            stream.flush()
            os.fchmod(stream.fileno(), row['mode'])
            os.utime(stream.fileno(), ns=(row['mtime_ns'],) * 2)
            os.fsync(stream.fileno())
            stream.close()
            os.replace(temporary, output / row['name'])
            syncdir(output)
    finally:
        for temporary, stream in active.values():
            if not stream.closed:
                stream.close()
    return {'restored_files': len(data['files']), 'output_directory': str(output)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('create', 'verify', 'retire', 'restore'))
    parser.add_argument('--source-dir')
    parser.add_argument('--archive-dir')
    parser.add_argument('--index')
    parser.add_argument('--index-sha256')
    parser.add_argument('--output-directory')
    parser.add_argument('--phase-lock', required=True)
    args = parser.parse_args()
    lock_path = bounded(args.phase_lock)
    with lock_path.open('a') as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        if args.action == 'create':
            result = create(args.source_dir, args.archive_dir)
        elif args.action == 'verify':
            result = verify(Path(args.index), args.index_sha256)
        elif args.action == 'retire':
            result = retire(Path(args.index), args.index_sha256)
        else:
            result = restore(Path(args.index), args.index_sha256, args.output_directory)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
