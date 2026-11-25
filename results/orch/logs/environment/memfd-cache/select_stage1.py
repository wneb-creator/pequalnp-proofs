from pathlib import Path
import hashlib
import json
import os
import stat

job = Path('/tmp/oec/pequalnp-pilot-144/memfd-cache')
root = Path('/tmp/oec/pequalnp-pilot-144/toolchain/lean-4.36.0-linux')
candidates = []
for directory, _, files in os.walk(root / 'lib' / 'lean'):
    for name in files:
        path = Path(directory) / name
        if not name.endswith(('.olean.private', '.ir', '.a')) or path.is_symlink():
            continue
        st = path.stat()
        if stat.S_ISREG(st.st_mode):
            candidates.append((st.st_size, path))
candidates.sort(reverse=True)
records = []
total = 0
for size, path in candidates:
    if total >= 2 * 1024**3:
        break
    st = path.stat()
    digest = hashlib.file_digest(path.open('rb'), 'sha256').hexdigest()
    records.append(dict(path=str(path.relative_to(root)), size=size, sha256=digest,
                        mode=stat.S_IMODE(st.st_mode), atime_ns=st.st_atime_ns,
                        mtime_ns=st.st_mtime_ns))
    total += size
(job / 'stage1.json').write_text(json.dumps(dict(root=str(root), total=total,
                                              files=records), indent=2) + '\n')
(job / 'stage1.files0').write_bytes(b''.join(r['path'].encode() + b'\0' for r in records))
print('Selected', len(records), 'immutable artifacts;', total, 'bytes')
print('Source root:', root)
