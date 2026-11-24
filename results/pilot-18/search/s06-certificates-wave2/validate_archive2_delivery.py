#!/usr/bin/env python3
"""Read-only verification of archive2 tar, all files and omitted CNF recipes."""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

O = Path('/tmp/oec/pequalnp-pilot-18/orch/S06')
A = O / 'archive2-final'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


command = ['python3', str(O / 'restore_archive2_cnfs.py'), str(A),
           '/tmp/oec/pequalnp-pilot-18/original-dag-strong/original.cnf', '--verify-only']
with (O / 'archive2-final-validation.stdout').open('xb') as out, (O / 'archive2-final-validation.stderr').open('xb') as err:
    completed = subprocess.run(command, stdout=out, stderr=err)
assert completed.returncode == 0
manifest = json.loads((A / 'manifest.json').read_text())
expected = {entry['path']: entry for entry in manifest['files']}
expected['manifest.json'] = {'sha256': sha(A / 'manifest.json'), 'bytes': (A / 'manifest.json').stat().st_size}
seen = set()
with tarfile.open(O / 'archive2-final.tar.gz', 'r:gz') as tar:
    for member in tar:
        assert member.isfile() and not member.issym() and not member.islnk()
        relative = Path(member.name)
        assert not relative.is_absolute() and '..' not in relative.parts
        assert member.name not in seen
        seen.add(member.name)
        raw = tar.extractfile(member).read()
        binding = expected[member.name]
        assert len(raw) == binding['bytes'] and hashlib.sha256(raw).hexdigest() == binding['sha256']
        assert not raw.startswith(b'\x7fELF') and relative.suffix not in ['.pyc', '.o', '.so']
        if relative.suffix == '.cnf':
            assert len(raw) <= 65536
assert seen == set(expected)
real_review = A / 'scratch/orch/S08/offline-real-case13-review/review.json'
assert sha(real_review) == 'c1a22439752d28b1a1640d87553de7ae14246a8ab697fd80775f6495a9534f99'
record = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'status': 'PASS',
          'command': command, 'exit_code': completed.returncode,
          'source_sha256': sha(Path(__file__)), 'manifest_sha256': sha(A / 'manifest.json'),
          'tar_sha256': sha(O / 'archive2-final.tar.gz'), 'tar_members': len(seen),
          'all_tar_members_regular_and_hash_bound': True,
          'reconstructed_large_cnfs': manifest['restorable_large_cnf_count'],
          'small_fixture_cnfs': manifest['small_raw_cnf_count'], 'large_raw_cnfs': 0,
          'compiled_binaries': 0, 'real_control_independent_review_sha256': sha(real_review),
          'stdout_sha256': sha(O / 'archive2-final-validation.stdout'),
          'stderr_sha256': sha(O / 'archive2-final-validation.stderr'), 'worker_launch': False}
(O / 'archive2-final-validation.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
