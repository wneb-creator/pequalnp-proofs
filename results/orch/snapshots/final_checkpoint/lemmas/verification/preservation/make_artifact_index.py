from pathlib import Path
import datetime
import gzip
import hashlib
import json
import subprocess

repo = Path('/workspace/pequalnp-proofs')
base = repo / 'results/orch'

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def files(args):
    result = subprocess.run(['rg', '--files', *args], cwd=repo,
                            capture_output=True, text=True, check=True)
    return result.stdout.splitlines()

stored = {}
for name in files(['-g', 'MANIFEST.json', 'results/orch/snapshots']):
    path = repo / name
    for row in json.loads(path.read_text()):
        source = row.get('source', row['file'])
        item = path.parent / row['file']
        assert item.resolve().is_relative_to(repo)
        stored[(source, row['sha256'])] = (item, row)
tracked = set(subprocess.run(['git', 'ls-files', '--', 'results/orch/lemmas'],
    cwd=repo, capture_output=True, text=True, check=True).stdout.splitlines())
patterns = ['*.py', '*.cpp', '*.json', '*.jsonl', '*.stdout', '*.stderr',
            '*.out', '*.err', '*.md', '*.txt', '*.log', '*.lean', '*.cnf',
            '*.dimacs', '*.drat', '*.lrat', '*.gz']
args = []
for pattern in patterns:
    args.extend(['-g', pattern])
args.append('results/orch/lemmas')
listing = files(args)
listed = set(listing)
entries, missing = [], []
for name in sorted(listing):
    if name + '.gz' in listed:
        continue
    path = repo / name
    sha = digest(path)
    relative = path.relative_to(base).as_posix()
    if name in tracked:
        staged = subprocess.run(['git', '--no-pager', 'show', ':' + name], cwd=repo,
                                capture_output=True, check=True).stdout
        staged_sha = hashlib.sha256(staged).hexdigest()
        assert staged_sha == sha, 'Tracked worktree differs from staged blob: ' + name
        storage, encoding, storage_sha = name, 'identity', sha
    else:
        match = stored.get((relative, sha))
        if match is None:
            missing.append({'source': name, 'sha256': sha})
            continue
        item, row = match
        assert digest(item) == row.get('stored_sha256', row['sha256'])
        storage = item.relative_to(repo).as_posix()
        encoding = 'identity' if row['file'] == relative else 'gzip'
        storage_sha = row.get('stored_sha256', row['sha256'])
        if encoding == 'gzip':
            h = hashlib.sha256()
            with gzip.open(item, 'rb') as stream:
                for block in iter(lambda: stream.read(1024 * 1024), b''):
                    h.update(block)
            assert h.hexdigest() == sha
    entries.append({'source': name, 'sha256': sha, 'bytes': path.stat().st_size,
                    'storage': storage, 'encoding': encoding,
                    'storage_sha256': storage_sha})
assert not missing, json.dumps({'unpreserved_sources': missing}, indent=2)
output = {'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'scope': 'Storage index only. Compilation and correctness claims come from reviewed validation receipts, not this index.',
          'entries': entries}
(base / 'ARTIFACT_INDEX.json').write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps({'indexed_sources': len(entries),
                  'direct': sum(x['encoding'] == 'identity' and x['storage'] == x['source'] for x in entries),
                  'snapshot': sum(x['storage'] != x['source'] for x in entries),
                  'unpreserved': 0}))
