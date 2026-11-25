import fcntl
import hashlib
import json
import os
from pathlib import Path
import stat
import time

ROOT = Path('/workspace/pequalnp-proofs/lean/.lake/packages').resolve(strict=True)
OLD_STATE = Path('/tmp/oec/pequalnp-pilot-184/setup/artifact-memory')
STATE = Path('/tmp/oec/pequalnp-pilot-184/setup/artifact-memory-adopted')
FLOOR = 200 * 1024 * 1024
OLD_PID = 13941
ROWS = {}
STATE.mkdir(exist_ok=True)
INBOX = STATE / 'requests'
INBOX.mkdir(exist_ok=True)


def process_identity(pid):
    try:
        raw = Path('/proc/' + str(pid) + '/stat').read_text()
        return raw[raw.rfind(')') + 2:].split()[19]
    except FileNotFoundError:
        return None


OLD_IDENTITY = process_identity(OLD_PID)
if OLD_IDENTITY is None:
    raise RuntimeError('old holder must remain alive during adoption')


def digest_fd(fd):
    result = hashlib.sha256()
    offset = 0
    while block := os.pread(fd, 1024 * 1024, offset):
        result.update(block)
        offset += len(block)
    return result.hexdigest()


def validate_path(raw):
    path = Path(raw)
    if not path.is_absolute() or '..' in path.parts:
        raise ValueError('noncanonical path')
    relative = path.relative_to(ROOT).parts
    if len(relative) < 6 or relative[1:5] != ('.lake', 'build', 'lib', 'lean'):
        raise ValueError('not structurally a cached package artifact')
    if path.parent.resolve(strict=True) != path.parent:
        raise ValueError('symlinked artifact parent')
    if not path.name.endswith(('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig')):
        raise ValueError('unexpected artifact suffix')
    return path


def verify_fd(fd, row):
    info = os.fstat(fd)
    if not stat.S_ISREG(info.st_mode) or info.st_size != row['size']:
        raise ValueError('adopted descriptor type/size mismatch')
    if fcntl.fcntl(fd, 1034) & 15 != 15:
        raise ValueError('descriptor not immutably sealed')
    if digest_fd(fd) != row['sha256']:
        raise ValueError('descriptor content mismatch')
    return info


def fsync_dir(path):
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def append_log(name, row):
    with (STATE / name).open('a') as out:
        out.write(json.dumps(row) + '\n')
        out.flush()
        os.fsync(out.fileno())


def status(phase):
    live = [row for row in ROWS.values() if row['fd'] is not None]
    temporary = STATE / 'status.tmp'
    temporary.write_text(json.dumps({'pid': os.getpid(), 'old_pid': OLD_PID,
                                     'phase': phase, 'files': len(live),
                                     'bytes': sum(row['size'] for row in live)}) + '\n')
    os.replace(temporary, STATE / 'status.json')


def adopt():
    source = [json.loads(line) for line in (OLD_STATE / 'manifest.jsonl').read_text().splitlines()]
    old_status = json.loads((OLD_STATE / 'status.json').read_text())
    if len(source) != old_status['files'] or sum(row['size'] for row in source) != old_status['bytes']:
        raise ValueError('old manifest and status disagree')
    for original in source:
        path = validate_path(original['path'])
        old_target = '/proc/' + str(OLD_PID) + '/fd/' + str(int(original['fd']))
        if original['target'] != old_target or not path.is_symlink() or os.readlink(path) != old_target:
            raise ValueError('old link changed or unexpected')
        if str(path) in ROWS:
            raise ValueError('duplicate old manifest path')
        before = path.stat()
        fd = os.open(old_target, os.O_RDONLY | os.O_CLOEXEC)
        try:
            info = verify_fd(fd, original)
            after = path.stat()
            if (before.st_dev, before.st_ino, before.st_size) != (info.st_dev, info.st_ino, info.st_size):
                raise ValueError('adoption changed inode')
            if (after.st_dev, after.st_ino, after.st_size) != (info.st_dev, info.st_ino, info.st_size):
                raise ValueError('old link changed during adoption')
        except Exception:
            os.close(fd)
            raise
        row = dict(original, old_target=old_target, old_fd=original['fd'], fd=fd,
                   target='/proc/' + str(os.getpid()) + '/fd/' + str(fd),
                   dev=info.st_dev, inode=info.st_ino)
        ROWS[str(path)] = row
        append_log('manifest.jsonl', row)
    if process_identity(OLD_PID) != OLD_IDENTITY:
        raise RuntimeError('old holder changed during adoption')
    status('adopted')


def migrate():
    for row in ROWS.values():
        path = validate_path(row['path'])
        if not path.is_symlink() or os.readlink(path) not in (row['old_target'], row['target']):
            raise ValueError('unexpected migration source')
        verify_fd(row['fd'], row)
    for row in ROWS.values():
        path = validate_path(row['path'])
        if os.readlink(path) == row['target']:
            continue
        temporary = path.with_name(path.name + '.adopt-link')
        if temporary.exists() or temporary.is_symlink():
            raise ValueError('temporary migration path already exists')
        try:
            temporary.symlink_to(row['target'])
            info = temporary.stat()
            if (info.st_dev, info.st_ino, info.st_size) != (row['dev'], row['inode'], row['size']):
                raise ValueError('new link identity mismatch')
            if not path.is_symlink() or os.readlink(path) != row['old_target']:
                raise ValueError('old link changed during migration')
            os.replace(temporary, path)
            fsync_dir(path.parent)
            append_log('migrated.jsonl', {'path': str(path), 'old_target': row['old_target'],
                                        'target': row['target'], 'sha256': row['sha256']})
        finally:
            if temporary.is_symlink():
                temporary.unlink()
    audit()
    status('migrated_and_audited')
    return {'migrated': len(ROWS)}


def audit():
    count = 0
    for row in ROWS.values():
        path = validate_path(row['path'])
        if row['fd'] is None:
            if path.is_symlink() or not stat.S_ISREG(path.stat().st_mode):
                raise ValueError('restored artifact is not regular')
            with path.open('rb') as stream:
                if path.stat().st_size != row['size'] or hashlib.file_digest(stream, 'sha256').hexdigest() != row['sha256']:
                    raise ValueError('restored artifact content mismatch')
        else:
            if not path.is_symlink() or os.readlink(path) != row['target']:
                raise ValueError('artifact does not target new holder')
            info = path.stat()
            if (info.st_dev, info.st_ino, info.st_size) != (row['dev'], row['inode'], row['size']):
                raise ValueError('artifact target inode mismatch')
            verify_fd(row['fd'], row)
        count += 1
    return {'verified': count}


def restore(spec):
    if process_identity(OLD_PID) == OLD_IDENTITY:
        raise RuntimeError('old holder must exit only after successful complete migration audit')
    maximum = int(spec['max_bytes'])
    restored_bytes = 0
    restored_files = 0
    candidates = sorted((row for row in ROWS.values() if row['fd'] is not None),
                        key=lambda row: row['size'], reverse=True)
    for row in candidates:
        if restored_bytes + row['size'] > maximum:
            continue
        path = validate_path(row['path'])
        available = os.statvfs(path.parent).f_bavail * os.statvfs(path.parent).f_frsize
        if available - row['size'] < FLOOR:
            break
        verify_fd(row['fd'], row)
        temporary = path.with_name(path.name + '.disk-restore')
        if temporary.exists() or temporary.is_symlink():
            raise ValueError('temporary disk restore path already exists')
        if path.is_symlink():
            if os.readlink(path) != row['target']:
                raise ValueError('unexpected restore source')
            try:
                with temporary.open('xb') as out:
                    offset = 0
                    while block := os.pread(row['fd'], 1024 * 1024, offset):
                        out.write(block)
                        offset += len(block)
                    out.flush()
                    os.fsync(out.fileno())
                with temporary.open('rb') as stream:
                    if temporary.stat().st_size != row['size'] or hashlib.file_digest(stream, 'sha256').hexdigest() != row['sha256']:
                        raise ValueError('disk copy verification failed')
                os.chmod(temporary, 0o644)
                os.utime(temporary, ns=(row['mtime_ns'], row['mtime_ns']))
                if not path.is_symlink() or os.readlink(path) != row['target']:
                    raise ValueError('restore source changed')
                os.replace(temporary, path)
                fsync_dir(path.parent)
            finally:
                if temporary.exists():
                    temporary.unlink()
        if path.is_symlink() or not stat.S_ISREG(path.stat().st_mode):
            raise ValueError('restored destination not regular')
        with path.open('rb') as stream:
            if path.stat().st_size != row['size'] or hashlib.file_digest(stream, 'sha256').hexdigest() != row['sha256']:
                raise ValueError('installed disk artifact verification failed')
        append_log('restored.jsonl', {'path': str(path), 'size': row['size'], 'sha256': row['sha256'],
                                     'old_target': row['target'], 'time': time.time()})
        os.close(row['fd'])
        row['fd'] = None
        restored_bytes += row['size']
        restored_files += 1
        status('restoring')
    status('restored_batch')
    return {'restored_files': restored_files, 'restored_bytes': restored_bytes}


def put_back(spec):
    # Reverse disk restoration after the verifier exits, so cached C/ilean
    # facets can be restored before any subsequent Lake build.
    maximum = int(spec['max_bytes'])
    moved_bytes = 0
    moved_files = 0
    for row in sorted((row for row in ROWS.values() if row['fd'] is None),
                      key=lambda row: row['size'], reverse=True):
        if moved_bytes + row['size'] > maximum:
            continue
        path = validate_path(row['path'])
        if path.is_symlink() or not stat.S_ISREG(path.stat().st_mode):
            raise ValueError('put-back source is not a regular file')
        before = path.stat()
        if before.st_size != row['size']:
            raise ValueError('put-back source size changed')
        fd = os.memfd_create('pequalnp-artifact', os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING)
        temporary = path.with_name(path.name + '.put-back-link')
        if temporary.exists() or temporary.is_symlink():
            os.close(fd)
            raise ValueError('temporary put-back path already exists')
        committed = False
        try:
            with path.open('rb') as source:
                while block := source.read(1024 * 1024):
                    remaining = memoryview(block)
                    while remaining:
                        written = os.write(fd, remaining)
                        remaining = remaining[written:]
            fcntl.fcntl(fd, 1033, 15)
            info = verify_fd(fd, row)
            after = path.stat()
            if (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns) != (
                    before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns):
                raise ValueError('put-back source changed while copying')
            target = '/proc/' + str(os.getpid()) + '/fd/' + str(fd)
            temporary.symlink_to(target)
            linked = temporary.stat()
            if (linked.st_dev, linked.st_ino, linked.st_size) != (info.st_dev, info.st_ino, info.st_size):
                raise ValueError('put-back link identity mismatch')
            os.replace(temporary, path)
            committed = True
            row.update(fd=fd, target=target, dev=info.st_dev, inode=info.st_ino)
            fsync_dir(path.parent)
            append_log('put-back.jsonl', row)
            moved_bytes += row['size']
            moved_files += 1
            status('putting_back')
        finally:
            if temporary.is_symlink():
                temporary.unlink()
            if not committed:
                os.close(fd)
    status('put_back_batch')
    return {'moved_files': moved_files, 'moved_bytes': moved_bytes}


adopt()
while True:
    for request in sorted(INBOX.glob('*.json')):
        result_path = STATE / (request.stem + '.result.json')
        if result_path.exists():
            continue
        try:
            spec = json.loads(request.read_text())
            if spec['action'] == 'migrate':
                result = migrate()
            elif spec['action'] == 'audit':
                result = audit()
            elif spec['action'] == 'restore':
                result = restore(spec)
            elif spec['action'] == 'put_back':
                result = put_back(spec)
            else:
                raise ValueError('unknown action')
        except Exception as exc:
            result = {'error': type(exc).__name__ + ': ' + str(exc)}
        result_path.write_text(json.dumps(result) + '\n')
    time.sleep(0.25)
