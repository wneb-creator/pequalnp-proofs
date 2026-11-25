from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
base=Path('/workspace/pequalnp-proofs/results/gct231/star-pencil-classification');scratch=Path('/tmp/oec/pequalnp-pilot-75/gct231/triangle-kernel-zero')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
man=base/'sha256.json';assert sha(man)=='bb183a2f820ea3ede274870dcd9ea1b947695b74ce6ed06582fa36b00f207cb3';expected=json.loads(man.read_text())
files={str(p.relative_to(base)):p for p in base.rglob('*') if p.is_file() and p!=man};assert len(files)==44 and set(files)==set(expected)
for name,p in files.items():
 assert not p.is_symlink() and sha(p)==expected[name]
 b=p.read_bytes();b.decode('utf8');assert b'\x00' not in b and not b.startswith((b'\x7fELF',b'MZ'))
 if (scratch/name).exists():assert b==(scratch/name).read_bytes(),name
assert sha(base/'StarPencilClassification.lean')=='7bdbee0dc04cb54742c6a0e3a60c474cbd5a9bc50dc1df6529bca5899db32603'
assert sha(base/'StarPencilClassification.first-corollary.lean')=='9cd27b8c23633b4efb7fa36f866a4f8b0633e43da64ba47b51f880928fef5fe9'
status=json.loads((base/'status.json').read_text());assert status['source_sha256']==sha(base/'StarPencilClassification.lean') and status['compile_status']=='PASS' and status['axiom_audit_status']=='PENDING_SEPARATE_RUN'
final=json.loads((base/'star-lean-build03.run.json').read_text());assert final['status']=='PASS' and final['returncode']==0 and final['wall_seconds']==52.08170968500053 and final['peak_group_rss_kib']==4342128
assert final['seconds_limit']==180 and final['resident_memory_mib_limit']==6144 and final['rss_sample_seconds']==0.5
assert (base/'star-lean-build03.log').read_bytes()==b''
first=json.loads((base/'star-lean-build01.run.json').read_text());second=json.loads((base/'star-lean-build02.run.json').read_text());assert first['status']=='UNKNOWN_RESIDENT_MEMORY_LIMIT' and second['status']=='FAIL'
log2=(base/'star-lean-build02.log').read_text();assert 'pow_eq_zero' in log2
assert (base/'star-lean-source-review.log').read_text().rstrip().endswith('PASS') and (base/'star-source-review.log').read_text().rstrip().endswith('PASS')
replay=json.loads((base/'star-lowdegree-replay.log').read_text().splitlines()[0]);assert replay['verified_output_count']==97 and not replay['proved_nonzero_constant']
trace=json.loads((base/'star-lowdegree-trace.run.json').read_text());assert trace['status']=='COMPLETED' and trace['returncode']==0
readme=(base/'README.md').read_text();assert 'A separate axiom audit is pending' in readme and 'does not assert geometric chart coverage or prove the whole gap' in readme
print('Exact44-file manifest coverage/hash/text-only/full scratch-copy equality; both source snapshots and complete final/diagnostic logs/status consistent: PASS',flush=True)
print('Final checked source is7bdbee0..., empty log exit0,52.081710s/4342128KiB. Axiom audit remains explicitlypending. CAS replay says97 identities, not unit; final proof uses exact scalar identity. No source/compiler rerun.',flush=True)
print('Payload/inclusive bytes',sum(p.stat().st_size for p in files.values()),sum(p.stat().st_size for p in files.values())+man.stat().st_size,flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
