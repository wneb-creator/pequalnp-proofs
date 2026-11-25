from pathlib import Path
import gzip
import hashlib
import json
import re

directory = Path(__file__).parent
source = directory / 'triangle-qq-run.trace'
compressed = directory / 'triangle-qq-run.trace.gz'
digest = hashlib.sha256()
byte_count = 0
newline_count = 0
last_byte = b''
with source.open('rb') as src, compressed.open('xb') as dst:
    with gzip.GzipFile(filename='', mode='wb', fileobj=dst,
                       compresslevel=3, mtime=0) as archive:
        for block in iter(lambda: src.read(1024 * 1024), b''):
            digest.update(block)
            byte_count += len(block)
            newline_count += block.count(b'\n')
            last_byte = block[-1:]
            archive.write(block)
check = hashlib.sha256()
with gzip.open(compressed, 'rb') as stream:
    for block in iter(lambda: stream.read(1024 * 1024), b''):
        check.update(block)
assert check.digest() == digest.digest()
log = (directory / 'triangle-qq-run.log').read_text()
completed = [line for line in log.splitlines()
             if re.match(r'^\s+\d+\s+\d+\s+\d+\s+\d+\s+x\s+\d+', line)
             and re.search(r'\d+\.\d+\s+\|\s+\d+\.\d+\s*$', line)]
incomplete = [line for line in log.splitlines()
              if re.match(r'^\s+\d+\s+\d+\s+\d+\s+\d+\s+x\s+\d+', line)
              and line not in completed]
assert len(completed) == 30 and len(incomplete) == 1
result = {
    'raw_bytes': byte_count,
    'raw_sha256': digest.hexdigest(),
    'raw_newline_count': newline_count,
    'raw_ends_with_newline': last_byte == b'\n',
    'compressed_bytes': compressed.stat().st_size,
    'compressed_sha256': hashlib.sha256(compressed.read_bytes()).hexdigest(),
    'decompression_sha256_verified': True,
    'completed_rounds_with_timings': len(completed),
    'last_completed_round': completed[-1],
    'unfinished_round_log': incomplete[0],
    'basis_output_exists': (directory / 'triangle-qq-run.basis.json').exists(),
    'scope': 'Full interrupted trace, including its truncated final record; no replay or contradiction claimed.',
}
(directory / 'trace-preservation.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, sort_keys=True))
