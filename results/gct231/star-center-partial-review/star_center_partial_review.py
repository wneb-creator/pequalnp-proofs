from pathlib import Path
from datetime import datetime,timezone
import gzip,hashlib,json,re
base=Path('/workspace/pequalnp-proofs/results/gct231/star-center-r1-progress01')
inputfile=base.parent/'star-center-input/neogb-star-full-center-p1009.in'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
man=base/'sha256.json';mh=sha(man);assert mh.startswith('80ffe4c0')
expected=json.loads(man.read_text());files={p.name:p for p in base.iterdir() if p.is_file() and p!=man}
assert len(files)==5 and set(files)==set(expected)
for name,p in files.items():assert not p.is_symlink() and sha(p)==expected[name]
print('Exact5-file coverage/all hashes; manifest SHA256',mh,flush=True)
record=json.loads((base/'preservation.json').read_text());meta=json.loads((base/'snapshot-metadata.json').read_text());launch=json.loads((base/'launch.json').read_text())
assert record['metadata']==meta
assert (meta['sequence'],meta['round'],meta['nvars'],meta['characteristic'],meta['original_generators'],meta['original_terms'],meta['appended_basis_rows'],meta['appended_basis_terms'])==(2,79,18,1009,31,3600,414,999649)
assert meta['available_basis_rows']-meta['appended_basis_rows']==meta['omitted_basis_rows']==1193
assert meta['available_basis_terms']-meta['appended_basis_terms']==meta['omitted_basis_terms']==23360004
assert meta['derived_term_budget']==1000000 and meta['appended_basis_terms']<=meta['derived_term_budget']
assert launch['input_sha256']==launch['base_input_sha256']==sha(inputfile)=='2fa7c351ed1936e1f692cf06eb791c812748653e5e96ef76f0d0048ef7c864f6'
assert launch['base_generators']==31 and launch['command'][-1]=='31'
assert launch['binary_sha256']=='d6f8f11dd46e613bf7b0cb3f357cb5128d60a440d221749dae67575abe734246'
assert launch['library_sha256']=='dcf664df8036b637aae4b064662017b4fe20983b0c71be74f4c0b7474270e12f'
with inputfile.open() as original:
 ih=list(map(int,original.readline().split()));il=list(map(int,original.readline().split()));originalrows=[]
 assert ih==[18,31,1009,3600] and len(il)==31 and sum(il)==3600
 for length in il:originalrows.append([tuple(map(int,original.readline().split())) for _ in range(length)])
 assert not original.read().strip()
digest=hashlib.sha256();rawbytes=0;termcount=0
with gzip.open(base/'snapshot.in.gz','rb') as f:
 def line():
  global rawbytes
  b=f.readline();digest.update(b);rawbytes+=len(b);return b
 header=list(map(int,line().split()));lengths=list(map(int,line().split()))
 assert header==[18,445,1009,1003249] and len(lengths)==445 and sum(lengths)==1003249
 assert lengths[:31]==il and sum(lengths[31:])==999649
 for rowidx,length in enumerate(lengths):
  seen=set()
  for termidx in range(length):
   values=tuple(map(int,line().split()));assert len(values)==20
   num,den,*powers=values;mon=tuple(powers)
   assert den>0 and den%1009 and num%1009 and all(e>=0 for e in powers) and mon not in seen
   seen.add(mon);termcount+=1
   if rowidx<31:
    old=originalrows[rowidx][termidx]
    assert values[2:]==old[2:] and num*pow(den,-1,1009)%1009==old[0]*pow(old[1],-1,1009)%1009
  assert length>0
 tail=f.read();digest.update(tail);rawbytes+=len(tail);assert not tail.strip()
assert termcount==1003249 and rawbytes==record['snapshot_bytes_uncompressed']==42011622
assert digest.hexdigest()==record['snapshot_sha256_uncompressed']=='556b3c1775a6994e297e27645d9257f3dc7f32cbef180069be0682d1dab1b498'
print('Complete gzip decompression/hash/42011622-byte length; all1003249 numeric terms and445 nonempty rows valid: PASS',flush=True)
print('Same31 original polynomials retained, with identical exponent order and coefficients modulo1009;414 appended rows/999649terms; metadata accounting/budget and reviewed engine/input binding: PASS',flush=True)
log=(base/'stdout-stderr-through-snapshot.log').read_text()
assert 'CHECKPOINT sequence=2 round=79 appended_rows=414 appended_terms=999649' in log
later=re.findall(r'CHECKPOINT sequence=(\d+) round=(\d+)',log)
print('Captured ongoing log contains checkpoint markers',later,flush=True)
assert 'Partial finite-field restart generating set, not a final basis or mathematical verdict.' in record['scope']
assert 'Log is the entire prefix captured during an ongoing run.' in record['scope']
print('Scope accurate: partial snapshot sequence2/round79; captured log extends beyond that snapshot to sequence3/round106 and an unfinished following round. No final solver verdict or consequence proof is inferred.',flush=True)
print('No live solver or original snapshot touched; no polynomial membership proof attempted.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
