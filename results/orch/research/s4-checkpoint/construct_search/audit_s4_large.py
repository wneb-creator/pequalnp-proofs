from pathlib import Path
import json,struct,itertools,math,hashlib,zstandard,time,sys,resource,random
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));degree=int(sys.argv[1]);root=Path('/tmp/oec/pequalnp-pilot-78/numeric/s4-hadamard');start=time.monotonic();chart=json.loads((root/'chart.json').read_text());actions=json.loads(Path('/tmp/oec/pequalnp-pilot-78/construct_search/s4-hadamard-actions.json').read_text());polys=[{tuple(m):c for m,c in f} for f in chart['polynomials']]
def unpack(path):
 with path.open('rb') as source,zstandard.ZstdDecompressor().stream_reader(source) as reader:return reader.read()
rows=[(g,tuple(m)) for g,m in json.loads(unpack(root/f'invariant-D{degree}-rows.json.zst'))];cols=[tuple(m) for m in json.loads(unpack(root/f'invariant-D{degree}-columns.json.zst'))];assert len(set(rows))==len(rows) and len(set(cols))==len(cols)
def act(m,ac):
 v=ac['variables'];return tuple(sorted(v[x][0] for x in m)),math.prod(v[x][1] for x in m)
gmaps=[]
for ac in actions:
 pairs=[]
 for f in polys:
  out={}
  for m,c in f.items():
   mm,ss=act(m,ac);out[mm]=out.get(mm,0)+ss*c
  matches=[(i,sgn) for i,g in enumerate(polys) for sgn in [1,-1] if out=={m:sgn*c for m,c in g.items()}]
  assert len(matches)==1;pairs.append(matches[0])
 gmaps.append(pairs)
coltrace=0;rowtrace=0
for ac,gmap in zip(actions,gmaps):
 seen=set();series=[1]+[0]*degree
 for initial in range(18):
  if initial in seen:continue
  n=initial;length=0;sign=1
  while n not in seen:
   seen.add(n);length+=1;sign*=ac['variables'][n][1];n=ac['variables'][n][0]
  new=[0]*(degree+1)
  for i,v in enumerate(series):
   for k in range((degree-i)//length+1):new[i+k*length]+=v*sign**k
  series=new
 cumulative=list(itertools.accumulate(series));coltrace+=cumulative[degree]
 rowtrace+=sum(sign*cumulative[degree-sum(chart['parameter_exponents'][i])] for i,(j,sign) in enumerate(gmap) if i==j)
assert coltrace==24*len(cols) and rowtrace==24*len(rows)
print('MOLIEN_COUNTS_PASS','COLUMNS',len(cols),'ROWS',len(rows),flush=True)
for m in cols:
 orbit={}
 for ac in actions:
  mm,sign=act(m,ac)
  if mm in orbit:assert orbit[mm]==sign
  orbit[mm]=sign
 assert min(orbit)==m
for gen,m in rows:
 orbit={}
 for ac,gmap in zip(actions,gmaps):
  mm,sgn=act(m,ac);gg,ss=gmap[gen];key=(gg,mm);sgn*=ss
  if key in orbit:assert orbit[key]==sgn
  orbit[key]=sgn
 assert min(orbit)==(gen,m)
print('ALL_REPRESENTATIVES_VALID_COMPLETE',flush=True)
sample=sorted(random.Random(23178+degree).sample(range(len(rows)),min(100,len(rows))));samples={r:{} for r in sample};wpath=root/f'solve-D{degree}-p1000000007.witness';respath=root/f'solve-D{degree}-p1000000007.result.json';w=None;p=1000000007
if wpath.exists() and respath.exists() and json.loads(respath.read_text())['exit']==0:
 w={int(k):int(v) for k,v in (line.split() for line in wpath.read_text().splitlines())};assert len(w)==len(cols) and w[cols.index(())]==1
residual=[0]*len(rows);digest=hashlib.sha256();entries=0
with (root/f'invariant-D{degree}.bin.zst').open('rb') as source,zstandard.ZstdDecompressor().stream_reader(source) as reader:
 header=reader.read(16);digest.update(header);nr,nc,nnz=struct.unpack('<IIQ',header);assert(nr,nc)==(len(rows),len(cols));buf=b''
 while True:
  chunk=reader.read(2**20)
  if not chunk:break
  digest.update(chunk);buf+=chunk;count=len(buf)//16;end=16*count
  for r,c,v in struct.iter_unpack('<IIq',buf[:end]):
   assert r<nr and c<nc
   if w is not None:residual[r]=(residual[r]+v*w[c])%p
   if r in samples:assert c not in samples[r];samples[r][c]=v
  entries+=count;buf=buf[end:]
 assert not buf and entries==nnz
colids={m:i for i,m in enumerate(cols)}
for r in sample:
 gen,m=rows[r];avg={}
 for mon,c in polys[gen].items():
  product=tuple(sorted(m+mon))
  for ac in actions:
   mm,sign=act(product,ac);avg[mm]=avg.get(mm,0)+sign*c
 expected={}
 for mon,value in avg.items():
  if mon not in colids:continue
  size=len({act(mon,ac)[0] for ac in actions});assert value*size%24==0
  if value:expected[colids[mon]]=value*size//24
 assert expected==samples[r],r
print('RAW_REYNOLDS_SAMPLES_PASS',len(sample),'BINARY_ENTRIES',nnz,flush=True)
if w is not None:assert not any(residual);print('FULL_DUAL_WITNESS_PASS',nr,nc,'MODULUS',p,flush=True)
else:print('DUAL_WITNESS_NOT_YET_AVAILABLE',flush=True)
print('PASS','UNCOMPRESSED_SHA256',digest.hexdigest(),'SECONDS',time.monotonic()-start,'PEAK_RSS_KIB',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,flush=True)
