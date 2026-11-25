from pathlib import Path
import datetime
import hashlib
import json

job = Path('/tmp/oec/pequalnp-pilot-144/memfd-cache')
root = Path('/workspace/pequalnp-proofs/lean/.lake/packages/mathlib/.lake/build')
baseline = set(json.loads((job / 'mathlib-cache-baseline.json').read_text()))
records = []
for path in sorted((root / 'ir/Mathlib').rglob('*')):
    if not path.is_file() or path.is_symlink():
        continue
    rel = str(path.relative_to(root))
    if rel in baseline or not path.name.endswith(('.c', '.c.hash', '.c.o', '.c.o.hash',
                                                 '.c.o.export', '.c.o.export.hash')):
        continue
    with path.open('rb') as src:
        digest = hashlib.file_digest(src, 'sha256').hexdigest()
    records.append(dict(path=rel, size=path.stat().st_size, sha256=digest))
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
(job / f'c-clean-{stamp}.json').write_text(json.dumps(records, indent=2) + '\n')
for record in records:
    (root / record['path']).unlink()
print('Removed only new generated C/object artifacts:', len(records),
      'bytes', sum(record['size'] for record in records))
