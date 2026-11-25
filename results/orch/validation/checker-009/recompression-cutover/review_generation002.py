import hashlib
import json
import os
from pathlib import Path
import subprocess

BASE = Path('/tmp/oec/pequalnp-pilot-45')
OLD = BASE / 'build-cache-compaction/generation-001'
NEW = BASE / 'build-cache-compaction/generation-002'
HERE = BASE / 'recompression-cutover'

def sha(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for data in iter(lambda: stream.read(1048576), b''):
            value.update(data)
    return value.hexdigest()

report = json.loads((NEW / 'staging-report.json').read_text())
assert report['status'] == 'PASS' and report['activation'] == 'not performed'
for path, pin in report['files'].items():
    assert Path(path).stat().st_size == pin['size'] and sha(path) == pin['sha256']
for path, pin in report['source_packs'].items():
    assert Path(path).stat().st_size == pin['size'] and sha(path) == pin['sha256']
assert sha(OLD / 'state/prepared.json') == report['source_prepared_sha256']
before = json.loads((OLD / 'state/prepared.json').read_text())['files']
after = json.loads((NEW / 'state/prepared.json').read_text())['files']
assert set(before) == set(after) and len(after) == 28998
strip = lambda row: {key: value for key, value in row.items() if key not in ('pack', 'offset', 'compressed')}
for path, row in after.items():
    assert strip(row) == strip(before[path])

old_config_path = BASE / 'resource-wrapper/shared-library-fallback/generation-001-config.json'
assert sha(old_config_path) == report['source_config_sha256']
old_config = json.loads(old_config_path.read_text())
new_config = json.loads((NEW / 'storage_config.json').read_text())
changed = {'state_dir', 'editor_index', 'editor_manifest', 'editor_pack'}
assert {k: v for k, v in old_config.items() if k not in changed} == {k: v for k, v in new_config.items() if k not in changed}
locks = [OLD / 'state/phase.lock', NEW / 'state/phase.lock', Path(old_config['phase_lock'])]
assert len({(p.stat().st_dev, p.stat().st_ino) for p in locks}) == 1

old_baseline = [json.loads(line) for line in (OLD / 'editor/manifest.jsonl').read_text().splitlines()]
new_baseline = [json.loads(line) for line in (NEW / 'editor/manifest.jsonl').read_text().splitlines()]
assert new_baseline == old_baseline
expected_index = []
for row in old_baseline:
    updated = after[row['path']]
    assert updated['pack'] == str(NEW / 'editor/data.zstpack')
    expected_index.append(f"{row['virtual']}\t{updated['mode']:o}\t{updated['size']}\t{updated['mtime_ns']}\t{updated['offset']}\t{updated['compressed']}\n")
assert (NEW / 'editor/index.tsv').read_text() == ''.join(expected_index)

checked = raw_bytes = 0
for label, pack in [('editor', NEW / 'editor/data.zstpack'), ('extra', NEW / 'state/extra.zstpack')]:
    rows = sorted((row for row in after.values() if row['pack'] == str(pack)), key=lambda row: row['offset'])
    offset = 0
    with (HERE / f'review-generation002-{label}-decoder.stderr').open('wb') as error:
        process = subprocess.Popen(['zstd', '-d', '-c', str(pack)], stdout=subprocess.PIPE, stderr=error)
        try:
            for row in rows:
                assert row['offset'] == offset
                offset += row['compressed']
                remaining = row['size']
                value = hashlib.sha256()
                while remaining:
                    data = process.stdout.read(min(remaining, 1048576))
                    assert data, 'short independent decoder output'
                    remaining -= len(data)
                    value.update(data)
                assert value.hexdigest() == row['sha256']
                checked += 1
                raw_bytes += row['size']
            assert process.stdout.read(1) == b''
        finally:
            process.stdout.close()
            status = process.wait()
        assert status == 0 and offset == pack.stat().st_size
    assert (HERE / f'review-generation002-{label}-decoder.stderr').stat().st_size == 0
assert checked == 28998
print(json.dumps({'status': 'PASS', 'frames': checked, 'raw_bytes': raw_bytes,
                  'raw_metadata': 'identical', 'baseline_rows': len(new_baseline),
                  'source_packs': 'unchanged', 'shared_lock': 'same inode',
                  'independent_decoder': 'zstd CLI; all frames consumed exactly',
                  'staging_report_sha256': sha(NEW / 'staging-report.json')}, sort_keys=True))
