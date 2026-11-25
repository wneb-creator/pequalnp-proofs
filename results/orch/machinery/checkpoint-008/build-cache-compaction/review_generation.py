from pathlib import Path
import collections
import gzip
import hashlib
import json
import os
import stat
import subprocess

base = Path('/tmp/oec/pequalnp-pilot-45/build-cache-compaction')
transaction = base / 'transaction-001'
generation = base / 'generation-001'

def read_json(path):
    opener = gzip.open if str(path).endswith('.gz') else open
    with opener(path, 'rt') as stream:
        return json.load(stream)

def sha(path):
    result = hashlib.sha256()
    with open(path, 'rb') as stream:
        for chunk in iter(lambda: stream.read(1048576), b''):
            result.update(chunk)
    return result.hexdigest()

status = read_json(transaction / 'status.json')
plan = read_json(transaction / 'plan.json.gz')
assert status['status'] == 'staged'
assert sha(transaction / 'plan.json.gz') == status['plan_sha256']
old = read_json(transaction / 'original-prepared.json.gz')['files']
config = read_json(generation / 'storage_config.json')
old_config = read_json(transaction / 'original-config.json')
rows = read_json(Path(config['state_dir']) / 'prepared.json')['files']
removed = {row['path'] for row in plan['files']}
assert len(removed) == len(plan['files']) == 71764
assert len(old) == 100760 and len(rows) == 28996
assert set(rows) == set(old) - removed
for path in removed:
    assert not Path(path).exists() and not Path(path).is_symlink()
for path, expected in plan['source_hashes'].items():
    assert sha(path) == expected
changed = {'state_dir', 'editor_index', 'editor_manifest', 'editor_pack'}
assert {k: v for k, v in config.items() if k not in changed} == {k: v for k, v in old_config.items() if k not in changed}
old_lock = (Path(old_config['state_dir']) / 'phase.lock').stat()
new_lock = (Path(config['state_dir']) / 'phase.lock').stat()
assert (old_lock.st_dev, old_lock.st_ino) == (new_lock.st_dev, new_lock.st_ino)

groups = collections.defaultdict(dict)
live_bytes = 0
for path, row in rows.items():
    assert row['path'] == path
    for key in ('size', 'sha256', 'mode', 'mtime_ns'):
        assert row[key] == old[path][key]
    current = Path(path)
    assert current.is_file() and not current.is_symlink()
    before = current.stat()
    assert (before.st_size, stat.S_IMODE(before.st_mode), before.st_mtime_ns) == (row['size'], row['mode'], row['mtime_ns'])
    assert sha(current) == row['sha256']
    after = current.stat()
    assert (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) == (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
    frame = (row['compressed'], row['size'], row['sha256'])
    previous = groups[row['pack']].setdefault(row['offset'], frame)
    assert previous == frame
    live_bytes += row['size']

pack_results = []
for pack, frames in groups.items():
    assert Path(pack).is_relative_to(generation)
    with open(pack, 'rb') as source:
        child = subprocess.Popen(['/usr/bin/zstd', '-q', '-d', '-c'], stdin=source,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        offset = raw_total = 0
        try:
            for start, (compressed, raw_size, expected) in sorted(frames.items()):
                assert start == offset
                result = hashlib.sha256()
                remaining = raw_size
                while remaining:
                    chunk = child.stdout.read(min(remaining, 1048576))
                    assert chunk
                    result.update(chunk)
                    remaining -= len(chunk)
                assert result.hexdigest() == expected
                offset += compressed
                raw_total += raw_size
            assert not child.stdout.read(1)
            error = child.stderr.read()
            assert child.wait() == 0 and not error
        finally:
            if child.poll() is None:
                child.terminate()
                child.wait()
    assert offset == Path(pack).stat().st_size
    pack_results.append({'path': pack, 'compressed_bytes': offset, 'frames': len(frames),
                         'decoded_bytes': raw_total, 'sha256': sha(pack)})

index = {}
with open(config['editor_index']) as stream:
    for line in stream:
        fields = line.rstrip('\n').split('\t')
        assert len(fields) == 6 and fields[0] not in index
        index[fields[0]] = fields[1:]
baseline = set()
with open(config['editor_manifest']) as stream:
    for line in stream:
        item = json.loads(line)
        path = item['path']
        assert path in rows and path not in baseline
        baseline.add(path)
        row = rows[path]
        assert row['pack'] == config['editor_pack']
        for key in ('size', 'sha256', 'mode', 'mtime_ns'):
            assert item[key] == row[key]
        assert index.pop(item['virtual']) == [format(row['mode'], 'o'), str(row['size']),
                                             str(row['mtime_ns']), str(row['offset']), str(row['compressed'])]
assert not index

gates = []
for label in ('after-prune', 'after-stage'):
    gate = read_json(transaction / (label + '.json'))
    assert gate['passed'] is True and len(gate['commands']) == 2
    for number, record in enumerate(gate['commands']):
        assert record['status'] == 0
        assert record['argv'][1:3] == ['build', '--no-build']
        assert record['argv'][3:] == (['checklemma'] if number == 0 else ['+PEqualNP.Outside.R_meta_1768_45', '+PEqualNP.Defs'])
        out = transaction / f'{label}-{number}.stdout'
        err = transaction / f'{label}-{number}.stderr'
        assert sha(out) == record['stdout_sha256'] and sha(err) == record['stderr_sha256']
        stderr_text = err.read_text()
        assert stderr_text in ('', 'warning: mathlib: repository has local changes:\n  /workspace/pequalnp-proofs/lean/.lake/packages/mathlib\n')
        last = out.read_text().strip().splitlines()[-1]
        assert last.startswith('All targets up-to-date (')
        gates.append({'phase': label, 'target_index': number, 'last_line': last,
                      'stderr': stderr_text.strip()})

print(json.dumps({'status': 'PASS', 'retained_files': len(rows), 'retained_logical_bytes': live_bytes,
                  'pruned_files': len(removed), 'baseline_files': len(baseline),
                  'original_config_and_packs': 'hashes unchanged', 'phase_lock': 'same device and inode',
                  'prepared_sha256': sha(Path(config['state_dir']) / 'prepared.json'),
                  'packs': pack_results, 'gates': gates}, indent=2))
