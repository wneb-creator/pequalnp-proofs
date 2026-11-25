from pathlib import Path
import json,hashlib,itertools,time
base=Path('/tmp/oec/pequalnp-pilot-121/components2056');reports=[];t=time.monotonic()
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1<<20):h.update(b)
 return h.hexdigest()
for label in ['target63','control67']:
 stem='v5-nonread-'+label;prefix=base/(stem+'-seed67warm');phase=json.loads(prefix.with_suffix('.phase.json').read_text());rawmask=prefix.with_suffix('.mask.bin').read_bytes();nv=phase['variables'];nc=phase['clauses']
 assert len(rawmask)==(nv+7)//8 and hashlib.sha256(rawmask).hexdigest()==phase['mask_sha256']
 flips=[0]+[(rawmask[(i-1)//8]>>((i-1)%8))&1 for i in range(1,nv+1)]
 assert digest((base/stem).with_suffix('.cnf'))==phase['original_cnf_sha256']
 assert digest((base/stem).with_suffix('.mapping.json'))==phase['mapping_sha256']
 assert digest(prefix.with_suffix('.cnf'))==phase['warm_cnf_sha256']
 native=None
 if label=='control67':
  native=[None]*(nv+1);sat=False;sol=base/(stem+'-seed67warm-checked.sol')
  for line in sol.read_text().splitlines():
   if line.startswith('s '):sat=line=='s SATISFIABLE'
   if line.startswith('v '):
    for x in map(int,line.split()[1:]):
     if x:assert native[abs(x)] is None or native[abs(x)]==(x>0);native[abs(x)]=x>0
  assert sat and all(x is not None for x in native[1:]);original=[None]+[bool(native[i]^flips[i]) for i in range(1,nv+1)]
 failures=[];count=0
 with (base/stem).with_suffix('.cnf').open('rb') as a,prefix.with_suffix('.cnf').open('rb') as b:
  assert a.readline().split()==b.readline().split()==[b'p',b'cnf',str(nv).encode(),str(nc).encode()]
  for count,(l,r) in enumerate(itertools.zip_longest(a,b),1):
   assert l is not None and r is not None
   aa=list(map(int,l.split()));bb=list(map(int,r.split()));assert aa[-1]==bb[-1]==0
   assert [(-v if v and flips[abs(v)] else v) for v in aa]==bb
   if not any(v>0 for v in bb[:-1]):failures.append({'index':count,'literals':aa[:-1]})
   if native is not None:
    assert any(native[abs(v)]==(v>0) for v in bb[:-1])
    assert any(original[abs(v)]==(v>0) for v in aa[:-1])
 assert count==nc and failures==phase['violated_original_clauses']
 if label=='target63':assert [x['index'] for x in failures]==[2049893,2050020,2050147,2050274]
 else:assert not failures
 reports.append({'label':label,'variables':nv,'clauses_compared_and_checked':count,'exact_literal_sign_renaming':True,'phase_failures':failures,'native_and_inverse_model_all_clauses_checked':native is not None,'native_model_sha256':digest(sol) if native is not None else None,'warm_cnf_sha256':phase['warm_cnf_sha256'],'mask_sha256':phase['mask_sha256']})
q=Path('/tmp/oec/pequalnp-pilot-121/component-seed67-phase-independent-review.json');q.write_text(json.dumps({'status':'PASS independent full original/warm clause sign equivalence, warm phase and actual native/inverse assignments','scope':'Optional67-preferred component preparation; no63 target result; decoded candidate wrapper comparison separately required','reports':reports,'elapsed_seconds':time.monotonic()-t},indent=2)+'\n');print(q.read_text())
