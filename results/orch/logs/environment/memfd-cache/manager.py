from pathlib import Path
import fcntl
import hashlib
import json
import os
import signal
import sys
import traceback

manifest_path = Path(sys.argv[1])
manifest = json.loads(manifest_path.read_text())
root = Path(manifest['root'])
state_path = manifest_path.with_suffix('.state.json')
state = dict(pid=os.getpid(), status='starting', bytes=0, files=[])
fds = []

def save():
    tmp = state_path.with_suffix('.tmp')
    tmp.write_text(json.dumps(state, indent=2) + '\n')
    tmp.replace(state_path)

save()
try:
    for record in manifest['files']:
        path = root / record['path']
        assert not path.is_symlink() and path.is_file(), str(path)
        fd = os.memfd_create(path.name, os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING)
        fds.append(fd)
        digest = hashlib.sha256()
        with path.open('rb') as src, os.fdopen(os.dup(fd), 'wb') as dst:
            while chunk := src.read(1024**2):
                digest.update(chunk)
                dst.write(chunk)
        assert digest.hexdigest() == record['sha256'], str(path)
        assert os.fstat(fd).st_size == record['size'], str(path)
        os.fchmod(fd, record['mode'])
        os.utime(fd, ns=(record['atime_ns'], record['mtime_ns']))
        # Constants verified in installed Linux fcntl headers during the prototype.
        fcntl.fcntl(fd, 1033, 15)
        with open(f'/proc/{os.getpid()}/fd/{fd}', 'rb') as check:
            assert hashlib.file_digest(check, 'sha256').hexdigest() == record['sha256']
        replacement = path.with_name(path.name + '.memfd-stage')
        replacement.symlink_to(f'/proc/{os.getpid()}/fd/{fd}')
        replacement.replace(path)
        state['files'].append(dict(path=record['path'], fd=fd))
        state['bytes'] += record['size']
        if len(state['files']) % 100 == 0:
            save()
            print('Migrated', len(state['files']), 'files;', state['bytes'], 'bytes', flush=True)
    state['status'] = 'ready'
    save()
    print('READY PID', os.getpid(), 'files', len(state['files']), 'bytes', state['bytes'], flush=True)
except BaseException:
    state['status'] = 'migration-error-manager-retained'
    save()
    traceback.print_exc()
    print('Manager stays alive to preserve migrated artifacts.', flush=True)
while True:
    signal.pause()
