from pathlib import Path
from datetime import datetime,timezone
import gzip,hashlib,json,re
root=Path('/tmp/oec/pequalnp-pilot-75/gct231');archive=Path('/workspace/pequalnp-proofs/results/gct231')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
configs=[('grouped-subset-r2-final','3a5b7a268865520ef6754466e8a3e076887c39d77ab7258e227eac63013e2ac5',1800,4096,2450,425,998869,27,261),('star-center-r1-final','0fc8f15c836ef0784ff61cec6a3eb1509df3126e90e801d6fe63ce655f58a3f6',900,2048,3600,418,999920,14,198)]
for name,mh,seconds,memory,ot,ar,at,sequence,roundno in configs:
 base=archive/name;man=base/'sha256.json';assert sha(man)==mh
 expected=json.loads(man.read_text());files={p.name:p for p in base.iterdir() if p.is_file() and p!=man};assert len(files)==7 and set(files)==set(expected)
 for rel,p in files.items():
  assert not p.is_symlink() and sha(p)==expected[rel]
  if rel!='snapshot.in.gz':p.read_bytes().decode('utf8')
 d=json.loads((base/'result.json').read_text());launch=json.loads((base/'launch.json').read_text());pres=json.loads((base/'preservation.json').read_text());meta=json.loads((base/'snapshot-metadata.json').read_text())
 assert all(d[k]==v for k,v in launch.items())
 assert d['status']==pres['run_status']=='UNKNOWN_TIME_LIMIT' and d['returncode'] is None
 assert (d['wall_limit_seconds'],d['memory_mib'],d['threads'],d['pairs'])==(seconds,memory,1,32)
 assert seconds<=d['seconds']<seconds+1 and 'unit_basis' not in d and 'basis_size' not in d
 assert d['checkpoint']['metadata']==pres['metadata']==meta
 assert (meta['nvars'],meta['characteristic'],meta['original_generators'],meta['original_terms'],meta['appended_basis_rows'],meta['appended_basis_terms'],meta['sequence'],meta['round'])==(18,1009,31,ot,ar,at,sequence,roundno)
 assert meta['available_basis_rows']-ar==meta['omitted_basis_rows'] and meta['available_basis_terms']-at==meta['omitted_basis_terms']
 assert at<=meta['derived_term_budget']==1000000
 assert d['binary_sha256']=='d6f8f11dd46e613bf7b0cb3f357cb5128d60a440d221749dae67575abe734246' and d['library_sha256']=='dcf664df8036b637aae4b064662017b4fe20983b0c71be74f4c0b7474270e12f'
 inp=Path(d['command'][1]);assert sha(inp)==d['input_sha256']==d['base_input_sha256']
 assert not Path(d['command'][2]).exists()
 with inp.open() as f:
  ih=list(map(int,f.readline().split()));il=list(map(int,f.readline().split()));original=[]
  assert ih==[18,31,1009,ot] and len(il)==31 and sum(il)==ot
  for length in il:original.append([tuple(map(int,f.readline().split())) for _ in range(length)])
  assert not f.read().strip()
 digest=hashlib.sha256();rawbytes=0;count=0
 with gzip.open(base/'snapshot.in.gz','rb') as f:
  def line():
   global rawbytes
   data=f.readline();digest.update(data);rawbytes+=len(data);return data
  h=list(map(int,line().split()));lens=list(map(int,line().split()))
  assert h==[18,31+ar,1009,ot+at] and len(lens)==31+ar and sum(lens)==ot+at and lens[:31]==il
  for rowidx,length in enumerate(lens):
   seen=set();assert length>0
   for termidx in range(length):
    values=tuple(map(int,line().split()));assert len(values)==20
    num,den,*mon=values;mon=tuple(mon)
    assert den>0 and den%1009 and num%1009 and all(e>=0 for e in mon) and mon not in seen
    seen.add(mon);count+=1
    if rowidx<31:
     old=original[rowidx][termidx];assert values[2:]==old[2:] and num*pow(den,-1,1009)%1009==old[0]*pow(old[1],-1,1009)%1009
  tail=f.read();digest.update(tail);rawbytes+=len(tail);assert not tail.strip()
 assert count==ot+at and digest.hexdigest()==pres['snapshot_sha256_uncompressed']==d['checkpoint']['sha256']
 assert rawbytes==pres['snapshot_bytes_uncompressed']==d['checkpoint']['bytes']
 prefix=Path(d['command'][5].removesuffix('.checkpoint'))
 assert (base/'stdout-stderr-complete.log').read_bytes()==prefix.with_suffix('.log').read_bytes()
 resultlog=(base/'wrapper-complete.log').read_text();assert 'UNKNOWN_TIME_LIMIT' in resultlog
 log=(base/'stdout-stderr-complete.log').read_text();assert f'CHECKPOINT sequence={sequence} round={roundno} appended_rows={ar} appended_terms={at}' in log
 assert 'reduce final basis' not in log
 assert 'not a Groebner basis or characteristic-zero proof' in pres['scope']
 print(name,'PASS7-file hashes/coverage; fullgzip',rawbytes,'bytes;',count,'numeric terms;',31+ar,'rows; original31 polynomial prefix modulo1009; metadata and complete log equality; status',d['status'],d['seconds'],'seconds',flush=True)
 print('Manifest',mh,'raw SHA256',digest.hexdigest(),flush=True)
print('No final basis, ideal-membership certificate or mathematical verdict. No live solver touched or rerun.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
