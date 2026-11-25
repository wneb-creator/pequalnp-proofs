import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import stat
import tarfile
import time

ROOT = Path('/workspace/pequalnp-proofs').resolve(strict=True)
TASK = Path('/tmp/oec/pequalnp-pilot-184').resolve(strict=True)
STATE = TASK / 'setup' / 'reclaim-metadata'
PLAN = TASK / 'setup' / 'reclaim-plan.json'
ARCHIVE = STATE / 'files.tar.gz'
MANIFEST = STATE / 'manifest.json.gz'
FLOOR = 200 * 1024 * 1024


def digest(stream):
    return hashlib.file_digest(stream, 'sha256').hexdigest()


def check_path(raw, group, must_exist=True):
    path = Path(raw)
    if not path.is_absolute() or '..' in path.parts:
        raise ValueError('noncanonical path')
    if path.parent.resolve(strict=True) != path.parent:
        raise ValueError('symlinked parent')
    if group == 'runtime_metadata':
        base = ROOT / 'lean' / '.lake' / 'packages'
        relative = path.relative_to(base).parts
        if len(relative) < 5 or relative[1:3] != ('.lake', 'build'):
            raise ValueError('invalid package artifact path')
        if not ((relative[3:5] == ('lib', 'lean') and path.name.endswith(('.hash', '.trace')))
                or (relative[3] == 'ir' and path.name.endswith('.c.hash'))):
            raise ValueError('not permitted metadata')
    elif group == 'generated_setup':
        path.relative_to(ROOT / 'lean' / '.lake' / 'build' / 'ir')
        if not path.name.endswith('.setup.json'):
            raise ValueError('not generated setup')
    elif group == 'public_census':
        if path != TASK / 'open-prs-retry.json':
            raise ValueError('unexpected census')
    else:
        raise ValueError('unknown group')
    if path.is_symlink():
        raise ValueError('symlink forbidden')
    if must_exist and not stat.S_ISREG(path.stat().st_mode):
        raise ValueError('not regular file')
    return path


def archive_name(path):
    if path.is_relative_to(ROOT):
        return 'repo/' + path.relative_to(ROOT).as_posix()
    return 'task/' + path.relative_to(TASK).as_posix()


def load_manifest():
    with gzip.open(MANIFEST, 'rt') as stream:
        rows = json.load(stream)
    seen = set()
    for row in rows:
        path = check_path(row['path'], row['group'], must_exist=False)
        if row['name'] != archive_name(path) or row['name'] in seen:
            raise ValueError('invalid archive mapping')
        seen.add(row['name'])
    return rows


def verify_archive(rows):
    expected = {row['name']: row for row in rows}
    seen = set()
    with tarfile.open(ARCHIVE, 'r:gz') as tar:
        for member in tar:
            if member.name not in expected or member.name in seen or not member.isfile():
                raise ValueError('unexpected archive member')
            row = expected[member.name]
            with tar.extractfile(member) as stream:
                if member.size != row['size'] or digest(stream) != row['sha256']:
                    raise ValueError('archive hash mismatch')
            seen.add(member.name)
    if seen != set(expected):
        raise ValueError('incomplete archive')


def prepare():
    STATE.mkdir(exist_ok=True)
    if ARCHIVE.exists() or MANIFEST.exists():
        raise ValueError('archive already exists')
    plan = json.loads(PLAN.read_text())
    groups = [('runtime_metadata', plan['runtime_metadata_files']),
              ('generated_setup', plan['generated_setup_files']),
              ('public_census', [str(TASK / 'open-prs-retry.json')])]
    rows = []
    for group, paths in groups:
        for raw in paths:
            path = check_path(raw, group)
            info = path.stat()
            with path.open('rb') as stream:
                sha = digest(stream)
            rows.append({'path': str(path), 'group': group, 'name': archive_name(path),
                         'size': info.st_size, 'sha256': sha, 'mode': stat.S_IMODE(info.st_mode),
                         'mtime_ns': info.st_mtime_ns, 'inode': info.st_ino, 'dev': info.st_dev})
    temporary = ARCHIVE.with_suffix('.tmp')
    with tarfile.open(temporary, 'w:gz', compresslevel=6) as tar:
        for row in rows:
            path = check_path(row['path'], row['group'])
            member = tarfile.TarInfo(row['name'])
            member.size = row['size']
            member.mode = row['mode']
            member.mtime = row['mtime_ns'] // 1000000000
            with path.open('rb') as stream:
                tar.addfile(member, stream)
            if os.statvfs(STATE).f_bavail * os.statvfs(STATE).f_frsize < FLOOR:
                raise RuntimeError('disk floor reached during archive')
    with temporary.open('rb') as stream:
        os.fsync(stream.fileno())
    os.replace(temporary, ARCHIVE)
    with gzip.open(MANIFEST, 'xt', compresslevel=6) as stream:
        json.dump(rows, stream)
    with MANIFEST.open('rb') as stream:
        os.fsync(stream.fileno())
    verify_archive(rows)
    print(json.dumps({'phase': 'prepared', 'files': len(rows), 'source_bytes': sum(r['size'] for r in rows),
                      'archive_bytes': ARCHIVE.stat().st_size}), flush=True)


def apply():
    rows = load_manifest()
    verify_archive(rows)
    # Complete preflight before removing even one original.
    for row in rows:
        path = check_path(row['path'], row['group'])
        info = path.stat()
        if (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns) != (
                row['dev'], row['inode'], row['size'], row['mtime_ns']):
            raise ValueError('source identity changed before reclaim')
        with path.open('rb') as stream:
            if digest(stream) != row['sha256']:
                raise ValueError('source content changed before reclaim')
    with (STATE / 'removed.jsonl').open('a') as log:
        for row in rows:
            path = check_path(row['path'], row['group'])
            info = path.stat()
            if (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns) != (
                    row['dev'], row['inode'], row['size'], row['mtime_ns']):
                raise ValueError('source changed during reclaim')
            path.unlink()
            log.write(json.dumps({'name': row['name'], 'time': time.time()}) + '\n')
        log.flush()
        os.fsync(log.fileno())
    print(json.dumps({'phase': 'applied', 'files': len(rows)}), flush=True)


def restore():
    rows = load_manifest()
    verify_archive(rows)
    expected = {row['name']: row for row in rows}
    with tarfile.open(ARCHIVE, 'r:gz') as tar:
        for member in tar:
            row = expected[member.name]
            path = check_path(row['path'], row['group'], must_exist=False)
            if path.exists():
                with path.open('rb') as stream:
                    if digest(stream) != row['sha256']:
                        raise ValueError('existing destination has changed; preserve it')
                continue
            temporary = path.with_name(path.name + '.restore-tmp')
            if temporary.exists() or temporary.is_symlink():
                raise ValueError('temporary restore path already exists')
            try:
                with temporary.open('xb') as out, tar.extractfile(member) as source:
                    while block := source.read(1024 * 1024):
                        out.write(block)
                    out.flush()
                    os.fsync(out.fileno())
                with temporary.open('rb') as stream:
                    if temporary.stat().st_size != row['size'] or digest(stream) != row['sha256']:
                        raise ValueError('restore verification failed')
                os.chmod(temporary, row['mode'])
                os.utime(temporary, ns=(row['mtime_ns'], row['mtime_ns']))
                os.replace(temporary, path)
            finally:
                if temporary.exists():
                    temporary.unlink()
    print(json.dumps({'phase': 'restored', 'files': len(rows)}), flush=True)


parser = argparse.ArgumentParser()
parser.add_argument('phase', choices=['prepare', 'verify', 'apply', 'restore'])
args = parser.parse_args()
if args.phase == 'prepare':
    prepare()
elif args.phase == 'apply':
    apply()
elif args.phase == 'restore':
    restore()
else:
    verify_archive(load_manifest())
    print('archive verified')
