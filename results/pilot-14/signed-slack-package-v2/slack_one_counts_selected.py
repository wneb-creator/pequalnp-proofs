from pathlib import Path
import json,itertools,functools,time,sys
P=Path(__file__).parent;d=json.loads((P/'Data414.json').read_text());n=414;mask=(1<<n)-1;full=(1<<(2*n))-1
canon=lambda x:(x^full) if (x>>477)&1 else x
sep=lambda x:((x>>n)^x)&mask
@functools.lru_cache(None)
def ops(a,b):return tuple(sorted(set(canon(x&y)for x in(a,a^full)for y in(b,b^full))))
raw=tuple(canon((int(a,0)<<n)|int(b,0))for a,b in d['raw']);first=sorted({z for a in raw for b in raw for z in ops(a,b)})
mode=sys.argv[1]if len(sys.argv)>1 else'memo';start=time.monotonic();rows=[]
selected=int(sys.argv[2])if len(sys.argv)>2 else -1
for index,z in enumerate(first):
 if selected>=0 and index!=selected:continue
 calls=hits=moves=0;cache={};depths={}
 def go(s,dep,v):
  global calls,hits,moves
  moves+=1
  if moves%65536==0 and time.monotonic()-start>90:raise RuntimeError('bounded diagnostic90s cap')
  cov=0
  for x in v:cov|=sep(x)
  if cov!=mask:return False
  calls+=1;depths[dep]=depths.get(dep,0)+1;key=(s,dep,v)
  if mode=='memo'and key in cache:hits+=1;return cache[key]
  if dep==0 or len(v)<=1:return True
  if s:
   for x in set(v):
    if go(0,dep,tuple(sorted(v+(x,)))):return True
  for i,j in itertools.combinations(range(len(v)),2):
   rest=tuple(x for k,x in enumerate(v)if k not in(i,j))
   for zz in ops(v[i],v[j]):
    if go(s,dep-1,tuple(sorted(rest+(zz,)))):return True
    if s:
     if go(0,dep-1,tuple(sorted(rest+(zz,v[i])))):return True
     if go(0,dep-1,tuple(sorted(rest+(zz,v[j])))):return True
  if mode=='memo':cache[key]=False
  return False
 result=go(1,4,tuple(sorted(raw+(z,))))
 row={'index':index,'signal':hex(z),'survives':result,'valid_calls':calls,'hits':hits,'unique_valid':calls-hits,'moves':moves,'depths':depths}
 rows.append(row)
 print(json.dumps(row),file=sys.stderr,flush=True)
print(json.dumps({'mode':mode,'first_count':len(first),'survivors':sum(r['survives']for r in rows),'total_calls':sum(r['valid_calls']for r in rows),'total_moves':sum(r['moves']for r in rows),'total_unique':sum(r['unique_valid']for r in rows),'worst':max(rows,key=lambda r:r['valid_calls']),'seconds':time.monotonic()-start,'rows':rows}),flush=True)
