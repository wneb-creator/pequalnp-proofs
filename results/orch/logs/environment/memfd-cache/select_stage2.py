from pathlib import Path
import hashlib
import json
import os
import stat

job = Path('/tmp/oec/pequalnp-pilot-144/memfd-cache')
root = Path('/workspace/pequalnp-proofs/lean/.lake/packages/mathlib/.lake/build')
baseline = sorted(str(p.relative_to(root)) for p in root.rglob('*') if p.is_file())
(job / 'mathlib-cache-baseline.json').write_text(json.dumps(baseline, indent=2) + '\n')
stage1 = json.loads((job / 'stage1.json').read_text())
limit = 7 * 1024**3 // 2 - stage1['total']
candidates = []
for directory, _, files in os.walk(root / 'lib/lean/Mathlib'):
    for name in files:
        path = Path(directory) / name
        if not name.endswith(('.olean.private', '.olean', '.ir', '.olean.server')) or path.is_symlink():
            continue
        st = path.stat()
        if stat.S_ISREG(st.st_mode):
            candidates.append((st.st_size, path))
candidates.sort(reverse=True)
records = []
total = 0
for size, path in candidates:
    if total + size > limit:
        continue
    st = path.stat()
    with path.open('rb') as src:
        digest = hashlib.file_digest(src, 'sha256').hexdigest()
    records.append(dict(path=str(path.relative_to(root)), size=size, sha256=digest,
                        mode=stat.S_IMODE(st.st_mode), atime_ns=st.st_atime_ns,
                        mtime_ns=st.st_mtime_ns))
    total += size
(job / 'stage2.json').write_text(json.dumps(dict(root=str(root), total=total,
                                              files=records), indent=2) + '\n')
(job / 'stage2.files0').write_bytes(b''.join(r['path'].encode() + b'\0' for r in records))
print('Selected', len(records), 'immutable artifacts;', total, 'bytes')
print('Combined anonymous allocation:', total + stage1['total'])
print('Source root:', root)
