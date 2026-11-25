from pathlib import Path
import hashlib
import json
import os
import signal
import subprocess
import sys
import tarfile

manifest_path = Path(sys.argv[1])
manifest = json.loads(manifest_path.read_text())
expected = {r['path']: r for r in manifest['files']}
root = Path(manifest['root'])
state = json.loads(manifest_path.with_suffix('.state.json').read_text())
proc = subprocess.Popen(['zstd', '-dc', sys.argv[2]], stdout=subprocess.PIPE)
restored = 0
with tarfile.open(fileobj=proc.stdout, mode='r|') as archive:
    for member in archive:
        assert member.isfile() and member.name in expected
        record = expected[member.name]
        path = root / member.name
        data = archive.extractfile(member)
        if not path.is_symlink():
            assert hashlib.file_digest(data, 'sha256').hexdigest() == record['sha256']
            continue
        assert str(path.readlink()).startswith(f'/proc/{state["pid"]}/fd/')
        temporary = path.with_name(path.name + '.restore-stage')
        digest = hashlib.sha256()
        with temporary.open('wb') as dst:
            while chunk := data.read(1024**2):
                digest.update(chunk)
                dst.write(chunk)
        assert digest.hexdigest() == record['sha256']
        temporary.chmod(record['mode'])
        os.utime(temporary, ns=(record['atime_ns'], record['mtime_ns']))
        temporary.replace(path)
        restored += 1
assert proc.wait() == 0
for record in expected.values():
    path = root / record['path']
    assert not path.is_symlink()
    with path.open('rb') as src:
        assert hashlib.file_digest(src, 'sha256').hexdigest() == record['sha256']
try:
    os.kill(state['pid'], signal.SIGTERM)
except ProcessLookupError:
    pass
state['status'] = 'restored'
manifest_path.with_suffix('.state.json').write_text(json.dumps(state, indent=2) + '\n')
print('Restored', restored, 'files; all hashes verified; manager terminated.')
