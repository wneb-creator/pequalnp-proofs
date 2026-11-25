import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import stat
import tarfile

ROOT = Path('/workspace/pequalnp-proofs/lean/.lake').resolve(strict=True)
TASK = Path('/tmp/oec/pequalnp-pilot-184/setup')
STATE = TASK / 'reclaim-facets'
ARCHIVE = STATE / 'files.tar.gz'
MANIFEST = STATE / 'manifest.json.gz'
EXECUTABLE = ROOT / 'build' / 'bin' / 'checklemma'
FLOOR = 200 * 1024 * 1024


def check_path(raw):
    path = Path(raw)
    if not path.is_absolute() or '..' in path.parts or path.parent.resolve(strict=True) != path.parent:
        raise ValueError('noncanonical artifact path')
    relative = path.relative_to(ROOT).parts
    if relative[0] == 'build':
        parts = relative[1:]
    elif len(relative) > 4 and relative[0] == 'packages' and relative[2:4] == ('.lake', 'build'):
        parts = relative[4:]
    else:
        raise ValueError('not a project/package build artifact')
    if not ((parts[0] == 'ir' and path.name.endswith('.c')) or
            (parts[:2] == ('lib', 'lean') and path.name.endswith('.ilean'))):
        raise ValueError('not a C or ilean artifact')
    if path.is_symlink():
        raise ValueError('symlink forbidden')
    if path.exists() and not stat.S_ISREG(path.stat().st_mode):
        raise ValueError('not a regular artifact')
    return path


def hash_file(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def load_manifest():
    with gzip.open(MANIFEST, 'rt') as source:
        rows = json.load(source)
    seen = set()
    for row in rows:
        path = check_path(row['path'])
        if row['name'] != path.relative_to(ROOT).as_posix() or row['name'] in seen:
            raise ValueError('invalid archive mapping')
        seen.add(row['name'])
    return rows


def verify(rows):
    expected = {row['name']: row for row in rows}
    seen = set()
    with tarfile.open(ARCHIVE, 'r:gz') as tar:
        for member in tar:
            if member.name not in expected or member.name in seen or not member.isfile():
                raise ValueError('unexpected archive member')
            row = expected[member.name]
            with tar.extractfile(member) as source:
                if member.size != row['size'] or hashlib.file_digest(source, 'sha256').hexdigest() != row['sha256']:
                    raise ValueError('archive hash mismatch')
            seen.add(member.name)
    if seen != set(expected):
        raise ValueError('incomplete archive')


def prepare():
    STATE.mkdir(exist_ok=True)
    if ARCHIVE.exists() or MANIFEST.exists():
        raise ValueError('archive already exists')
    plan = json.loads((TASK / 'reclaim-facets-plan.json').read_text())
    rows = []
    for entry in plan['files']:
        path = check_path(entry['path'])
        info = path.stat()
        rows.append({'path': str(path), 'name': path.relative_to(ROOT).as_posix(),
                     'size': info.st_size, 'sha256': hash_file(path), 'mode': stat.S_IMODE(info.st_mode),
                     'dev': info.st_dev, 'inode': info.st_ino, 'mtime_ns': info.st_mtime_ns})
    temporary = STATE / 'files.tmp'
    with tarfile.open(temporary, 'w:gz', compresslevel=6) as tar:
        for row in rows:
            member = tarfile.TarInfo(row['name'])
            member.size = row['size']
            member.mode = row['mode']
            member.mtime = row['mtime_ns'] // 1000000000
            with check_path(row['path']).open('rb') as source:
                tar.addfile(member, source)
            if os.statvfs(STATE).f_bavail * os.statvfs(STATE).f_frsize < FLOOR:
                raise RuntimeError('disk floor reached during archive creation')
    with temporary.open('rb') as source:
        os.fsync(source.fileno())
    os.replace(temporary, ARCHIVE)
    with gzip.open(MANIFEST, 'xt', compresslevel=6) as source:
        json.dump(rows, source)
    with MANIFEST.open('rb') as source:
        os.fsync(source.fileno())
    verify(rows)
    print(json.dumps({'phase': 'prepared', 'files': len(rows), 'bytes': sum(row['size'] for row in rows),
                      'archive_bytes': ARCHIVE.stat().st_size}), flush=True)


def verifier_identity(pid):
    base = Path('/proc') / str(pid)
    if (base / 'exe').resolve(strict=True) != EXECUTABLE.resolve(strict=True):
        raise ValueError('PID is not the genuine compiled checklemma executable')
    raw = (base / 'stat').read_text()
    return raw[raw.rfind(')') + 2:].split()[19]


def apply(pid):
    if not pid:
        raise ValueError('verifier PID is required')
    identity = verifier_identity(pid)
    rows = load_manifest()
    verify(rows)
    for row in rows:
        path = check_path(row['path'])
        info = path.stat()
        if (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns) != (
                row['dev'], row['inode'], row['size'], row['mtime_ns']) or hash_file(path) != row['sha256']:
            raise ValueError('artifact changed since verified archive')
    with (STATE / 'removed.jsonl').open('a') as log:
        for row in rows:
            if verifier_identity(pid) != identity:
                raise ValueError('verifier stopped or changed; restore facets before future builds')
            path = check_path(row['path'])
            info = path.stat()
            if (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns) != (
                    row['dev'], row['inode'], row['size'], row['mtime_ns']):
                raise ValueError('artifact changed during removal')
            path.unlink()
            log.write(json.dumps({'name': row['name'], 'verifier_pid': pid, 'verifier_start': identity}) + '\n')
        log.flush()
        os.fsync(log.fileno())
    print(json.dumps({'phase': 'applied', 'files': len(rows), 'verifier_pid': pid}), flush=True)


def restore():
    rows = load_manifest()
    verify(rows)
    expected = {row['name']: row for row in rows}
    with tarfile.open(ARCHIVE, 'r:gz') as tar:
        for member in tar:
            row = expected[member.name]
            path = check_path(row['path'])
            if path.exists():
                if hash_file(path) != row['sha256']:
                    raise ValueError('existing artifact changed; preserve it')
                continue
            available = os.statvfs(path.parent).f_bavail * os.statvfs(path.parent).f_frsize
            if available - row['size'] < FLOOR:
                raise RuntimeError('restore needs disk: first put restored oleans back into sealed memfds')
            temporary = path.with_name(path.name + '.facet-restore')
            if temporary.exists() or temporary.is_symlink():
                raise ValueError('temporary facet restore path already exists')
            try:
                with temporary.open('xb') as out, tar.extractfile(member) as source:
                    while block := source.read(1024 * 1024):
                        out.write(block)
                    out.flush()
                    os.fsync(out.fileno())
                if temporary.stat().st_size != row['size'] or hash_file(temporary) != row['sha256']:
                    raise ValueError('restored artifact copy mismatch')
                os.chmod(temporary, row['mode'])
                os.utime(temporary, ns=(row['mtime_ns'], row['mtime_ns']))
                os.replace(temporary, path)
            finally:
                if temporary.exists():
                    temporary.unlink()
    print(json.dumps({'phase': 'restored', 'files': len(rows)}), flush=True)


parser = argparse.ArgumentParser()
parser.add_argument('phase', choices=['prepare', 'verify', 'apply', 'restore'])
parser.add_argument('--verifier-pid', type=int)
args = parser.parse_args()
if args.phase == 'prepare':
    prepare()
elif args.phase == 'apply':
    apply(args.verifier_pid)
elif args.phase == 'restore':
    restore()
else:
    verify(load_manifest())
    print('archive verified')
