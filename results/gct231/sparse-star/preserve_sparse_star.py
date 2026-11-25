"""Preserve completed sparse-star diagnostics without changing earlier archives."""
from pathlib import Path
import hashlib
import json
import shutil

source = Path('/tmp/oec/pequalnp-pilot-75/gct231')
destination = Path('/workspace/pequalnp-proofs/results/gct231/sparse-star')
files = ['neogb_convert.py', 'review_neogb_input.py', 'preserve_sparse_star.py',
         'review_matroid_strata.py', 'matroid-strata-review.log',
         'neogb-star-full-qq-preflight.log']
for label in ['qq', 'p1009']:
    prefix = f'neogb-star-full-{label}'
    files.extend(prefix + suffix for suffix in [
        '.in', '.provenance.json', '-convert.log', '.log',
        '.result.json', '-wrapper.log'])
    result = json.loads((source / (prefix + '.result.json')).read_text())
    assert result['status'] in ['COMPLETED', 'UNKNOWN_TIME_LIMIT', 'ERROR_OR_RESOURCE_LIMIT']
    output = source / (prefix + '-basis.json')
    if result['status'] == 'COMPLETED':
        assert output.exists()
        files.append(output.name)
destination.mkdir(parents=True, exist_ok=True)
for name in files:
    old, new = source / name, destination / name
    if new.exists():
        assert new.read_bytes() == old.read_bytes(), f'Existing archive differs: {name}'
    else:
        shutil.copy2(old, new)
manifest = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(destination.iterdir())
            if p.is_file() and p.name != 'sha256.json'}
path = destination / 'sha256.json'
path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
print('Archived data files:', len(manifest))
print('Manifest SHA256:', hashlib.sha256(path.read_bytes()).hexdigest())
