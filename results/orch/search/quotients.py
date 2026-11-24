import json,itertools,time
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-31/random/near_one');out=Path('/tmp/oec/pequalnp-pilot-31/search')
def partitions(n):
 def rec(a,m):
  if len(a)==n:yield a;return
  for x in range(m+2):yield from rec(a+[x],max(m,x))
 yield from rec([0],0)
parts=list(partitions(8));print('partitions',len(parts),flush=True)
checked=0;valid=0;best=0
for p in sorted(base.glob('near-8-*.json')):
 d=json.loads(p.read_text());es=[tuple(e)for e in d['edges']];gs=d['gates'];n=d['n']
 for pm in parts:
  m=max(pm)+1
  if m<2 or m==n:continue
  if any(pm[i]==pm[j]for i,j in es):continue
  edges={tuple(sorted((pm[i],pm[j])))for i,j in es};hood=[0]*m
  for i,j in edges:hood[i]|=1<<j;hood[j]|=1<<i
  if any((hood[i]&hood[j]).bit_count()>=2 for i,j in itertools.combinations(range(m),2)):continue
  checked+=1;vals=[sum(1<<x for x in range(1<<m)if x>>i&1)for i in range(m)];mapping=list(pm);ng=[]
  for op,i,j in gs:
   a,b=mapping[i],mapping[j];v=(vals[a]|vals[b])if op=='or'else(vals[a]&vals[b])
   try:q=vals.index(v)
   except ValueError:q=len(vals);vals.append(v);ng.append([op,a,b])
   mapping.append(q)
  wanted=0
  for i,j in edges:wanted|=vals[i]&vals[j]
  final=mapping[d.get('output',n+len(gs)-1)]
  if vals[final]!=wanted:continue
  used=set()
  def visit(v):
   if v<m or v in used:return
   used.add(v);_,a,b=ng[v-m];visit(a);visit(b)
  visit(final);size=len(used)
  alpha=max(x.bit_count()for x in range(1<<m)if all(not(hood[i]&x)for i in range(m)if x>>i&1));tau=m-alpha;lower=len(edges)+tau-1;valid+=1
  if lower-size>best:
   best=lower-size;print('new gap',best,'file',p.name,'n',m,'E',len(edges),'tau',tau,'size',size,'partition',pm,flush=True)
  if size<lower:
   oldnew={i:i for i in range(m)};new=[]
   for z,(op,a,b)in enumerate(ng):
    if m+z in used:oldnew[m+z]=m+len(new);new.append([op,oldnew[a],oldnew[b]])
   rec={'source':str(p),'partition':pm,'n':m,'edges':list(edges),'tau':tau,'gates':new,'output':oldnew[final],'lower':lower,'full_table_verified':True};(out/'quotient-witness.json').write_text(json.dumps(rec,indent=2));print('WITNESS',json.dumps(rec),flush=True);raise SystemExit
 print(p.name,'checked',checked,'valid',valid,flush=True)
print('FINISHED','checked',checked,'valid',valid,'best improvement',best,flush=True)
