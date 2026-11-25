from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
base=Path('/workspace/pequalnp-proofs/results/gct231/star-center-input')
scratch=Path('/tmp/oec/pequalnp-pilot-75/gct231')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat())
man=base/'sha256.json';assert sha(man)=='43db6c750a8cc63f367d566ff5b54ebcc02109c45eaaff5c816be1c9f2c0542d'
expected=json.loads(man.read_text());files={str(p.relative_to(base)):p for p in base.rglob('*') if p.is_file() and p!=man}
assert len(files)==14 and set(files)==set(expected)
for rel,p in files.items():
 assert not p.is_symlink() and sha(p)==expected[rel]
 b=p.read_bytes();b.decode('utf8');assert b'\x00' not in b and not b.startswith((b'\x7fELF',b'MZ',b'PK\x03\x04'))
for name in ('star_center_elimination_review.py','star-center-elimination-review.log'):
 assert sha(base/name)==sha(scratch/name)
for label,want in [('qq','f962797d0daa4ddc6167aba4625804cd6d9b85323a3fca139d6fe25f744686ff'),('p1009','2fa7c351ed1936e1f692cf06eb791c812748653e5e96ef76f0d0048ef7c864f6')]:
 inp=base/f'neogb-star-full-center-{label}.in';assert sha(inp)==want
 prov=json.loads((base/f'neogb-star-full-center-{label}.provenance.json').read_text());assert prov['input_sha256']==want
 assert prov['source_sha256']==sha(base/'star-full-center-eliminated-equations.json')
 assert (base/f'neogb-star-full-center-{label}-preflight.log').is_file()
print('PASS exact14-file manifest coverage/hashes/text-only and independent reviews copied verbatim')
print('PASS both already-reviewed sparse input hashes/provenance and preflight logs')
print('Scope: coordinate/input archive only; no solver outcome included or asserted')
print('Finish UTC',datetime.now(timezone.utc).isoformat())
