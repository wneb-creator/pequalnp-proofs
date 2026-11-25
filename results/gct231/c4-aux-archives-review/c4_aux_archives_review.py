from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
root=Path('/workspace/pequalnp-proofs/results/gct231')
scratch=Path('/tmp/oec/pequalnp-pilot-75/gct231')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
for name,count,want in [('c4-U-route',40,'d96a269ec89ff2a1b3ea1f4b6be02d982a5b2e6cd6df523358909515cc398949'),('augmented-c4-small-batches',19,'1da49c356b698efec19b98ac2003649dc3672275b1ead8037c4a98a55bce0c11')]:
 base=root/name;man=base/'sha256.json';assert sha(man)==want
 expected=json.loads(man.read_text());files={str(p.relative_to(base)):p for p in base.rglob('*') if p.is_file() and p!=man}
 assert len(files)==count and set(files)==set(expected)
 for rel,p in files.items():
  assert not p.is_symlink() and sha(p)==expected[rel]
  raw=p.read_bytes();raw.decode('utf8');assert b'\x00' not in raw and not raw.startswith((b'\x7fELF',b'MZ',b'PK\x03\x04'))
 print(name,'exact manifest coverage/hashes/text-only PASS',count,want,flush=True)
 for p in base.glob('*.result.json'):
  d=json.loads(p.read_text());assert d['status']=='COMPLETED' and d['returncode']==0 and d['unit_basis'] and d['basis_size']==1
  assert d['threads']==1 and d['memory_mib']==1024
  assert d['library_sha256']=='557a320ab8d064e7c57ae7798b8574b1ffd70728390ae98fcbc4e378bd726711'
  assert d['binary_sha256']=='5b2450117bea1df00d2f6fadaca11666588fd9cb76fb2ec943fa939f724b7441'
  basis=base/Path(d['command'][2]).name;assert sha(basis)==d['output_sha256']
  b=json.loads(basis.read_text());assert b['characteristic']==1009 and len(b['basis'])==1 and len(b['basis'][0])==1 and int(b['basis'][0][0][0])==1 and b['basis'][0][0][1]==[0]*b['nvars']
  inp=(base if name=='c4-U-route' else root/'augmented-c4-cases23')/Path(d['command'][1]).name
  assert sha(inp)==d['input_sha256']
  stem=p.name.removesuffix('.result.json');assert (base/(stem+'.log')).is_file() and (base/(stem+'-wrapper.log')).is_file()
  if name=='c4-U-route':assert d['wall_limit_seconds']==120 and d['command'][-2:]==['32','1']
  else:assert d['wall_limit_seconds']==10 and d['command'][-2] in ['1','4']
 print(name,'all complete finite-field unit output/input hashes and run limits PASS',flush=True)
base=root/'c4-U-route'
for name in ['reduced_c4_Uzero_review.py','reduced-c4-Uzero-review.log','reduced_c4_Usaturation_review.py','reduced-c4-Usaturation-review.log']:
 assert sha(base/name)==sha(scratch/name)
print('Both independent algebra/input reviews archived verbatim: PASS',flush=True)
assert 'AssertionError' in (base/'reduced-c4-Uzero-classify.log').read_text()
assert 'CASE3 final linear' in (base/'reduced-c4-Uzero-classify2.log').read_text()
summary=json.loads((root/'augmented-c4-small-batches/augmented-batch-summary.json').read_text())
for row in summary['records']:
 case,pairs=row['case'],row['pairs'];folder=root/('augmented-c4-cases23' if pairs==32 else 'augmented-c4-small-batches')
 name=f'neogb-c4-augmented{case}-p1009-'+('r1' if pairs==32 else f'b{pairs}')
 d=json.loads((folder/(name+'.result.json')).read_text())
 rows=[tuple(map(int,m.groups())) for line in (folder/(name+'.log')).read_text().splitlines() if (m:=re.match(r'^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+) x (\d+)',line))]
 assert row['printed_pair_rounds']==len(rows)
 assert row['max_columns']==max(t[4] for t in rows)
 assert row['max_matrix_entries']==max(t[3]*t[4] for t in rows)
 assert row['max_degree']==max(t[0] for t in rows)==14
 assert row['seconds']==d['seconds'] and row['status']==d['status']=='COMPLETED' and row['unit_F1009']
 print('SUMMARY case',case,'pairs',pairs,'rounds',len(rows),'max columns',row['max_columns'],'seconds',row['seconds'],'PASS',flush=True)
print('Scope: finite-field units/timing only; U=0 classification remains conditional. No QQ unit inference or solver rerun.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
