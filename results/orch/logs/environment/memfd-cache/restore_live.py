from pathlib import Path
import argparse
import hashlib
import json
import os
import signal

parser = argparse.ArgumentParser(description='Restore verified artifacts from a live memfd manager.')
parser.add_argument('manifest')
parser.add_argument('--one-smallest', action='store_true', help='Restore one artifact; retain manager.')
args = parser.parse_args()
manifest_path = Path(args.manifest)
manifest = json.loads(manifest_path.read_text())
state_path = manifest_path.with_suffix('.state.json')
state = json.loads(state_path.read_text())
root = Path(manifest['root'])
fd_for = {r['path']: r['fd'] for r in state['files']}
records = manifest['files']
if args.one_smallest:
    records = [min((r for r in records if (root / r['path']).is_symlink()),
                   key=lambda r: r['size'])]
restored = 0
for record in records:
    path = root / record['path']
    if not path.is_symlink():
        with path.open('rb') as current:
            assert hashlib.file_digest(current, 'sha256').hexdigest() == record['sha256']
        continue
    source = f'/proc/{state["pid"]}/fd/{fd_for[record["path"]]}'
    assert str(path.readlink()) == source
    temporary = path.with_name(path.name + '.restore-live')
    digest = hashlib.sha256()
    with open(source, 'rb') as src, temporary.open('wb') as dst:
        while chunk := src.read(1024**2):
            digest.update(chunk)
            dst.write(chunk)
    assert digest.hexdigest() == record['sha256']
    assert temporary.stat().st_size == record['size']
    temporary.chmod(record['mode'])
    os.utime(temporary, ns=(record['atime_ns'], record['mtime_ns']))
    temporary.replace(path)
    restored += 1
    print('Restored', record['path'], record['size'], record['sha256'], flush=True)
if not args.one_smallest:
    for record in manifest['files']:
        path = root / record['path']
        assert not path.is_symlink()
        with path.open('rb') as src:
            assert hashlib.file_digest(src, 'sha256').hexdigest() == record['sha256']
    os.kill(state['pid'], signal.SIGTERM)
    state['status'] = 'restored-live'
else:
    state.setdefault('restored_live_paths', []).extend(r['path'] for r in records)
state_path.write_text(json.dumps(state, indent=2) + '\n')
print('Live restoration succeeded:', restored, 'artifact(s); manager retained:', args.one_smallest)
