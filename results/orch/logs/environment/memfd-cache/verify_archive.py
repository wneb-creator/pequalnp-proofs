from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tarfile

manifest = json.loads(Path(sys.argv[1]).read_text())
expected = {r['path']: r for r in manifest['files']}
proc = subprocess.Popen(['zstd', '-dc', sys.argv[2]], stdout=subprocess.PIPE)
seen = set()
with tarfile.open(fileobj=proc.stdout, mode='r|') as archive:
    for member in archive:
        assert member.isfile() and member.name in expected, member.name
        record = expected[member.name]
        data = archive.extractfile(member)
        assert hashlib.file_digest(data, 'sha256').hexdigest() == record['sha256']
        assert member.size == record['size'] and member.mode == record['mode']
        seen.add(member.name)
assert proc.wait() == 0
assert seen == expected.keys()
print('Archive content hashes, sizes and modes verified:', len(seen), 'files')
