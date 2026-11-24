import itertools,json,time
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-31/random');out=Path('/tmp/oec/pequalnp-pilot-31/search');started=time.time();checked=0;valid=0
paths=[base/'near-fano7.json']+sorted((base/'near_one').glob('near-8-*.json'))
pre={m:([sum(1<<x for x in range(1<<m)if x>>i&1)for i in range(m)],(1<<(1<<m))-1)for m in range(2,9)}
def substitutions(n):
 def rec(a,m):
  if len(a)==n:
   if 2<=m<n:yield a,m
   return
  for x in [-2,-1]+list(range(m+1)):yield from rec(a+[x],max(m,x+1))
 yield from rec([],0)
for path in paths:
 d=json.loads(path.read_text());n=d['n'];gates=d['gates']
 for sub,m in substitutions(n):
  checked+=1;inputs,full=pre[m];vals={-2:full,-1:0,**dict(enumerate(inputs))};byfun={v:k for k,v in vals.items()};ws=sub.copy();gs=[]
  for op,a,b in gates:
   i,j=ws[a],ws[b];v=(vals[i]|vals[j])if op=='or'else(vals[i]&vals[j])
   if v in byfun:k=byfun[v]
   else:k=m+len(gs);gs.append([op,i,j]);vals[k]=v;byfun[v]=k
   ws.append(k)
  end=ws[d.get('output',n+len(gates)-1)];f=vals[end]
  if f&1 or any(f>>(1<<i)&1 for i in range(m)):continue
  es=[(i,j)for i,j in itertools.combinations(range(m),2)if f>>((1<<i)|(1<<j))&1]
  if not es:continue
  hood=[0]*m;quad=0
  for i,j in es:hood[i]|=1<<j;hood[j]|=1<<i;quad|=inputs[i]&inputs[j]
  if quad!=f or any((hood[i]&hood[j]).bit_count()>=2 for i,j in itertools.combinations(range(m),2)):continue
  valid+=1;used=set()
  def visit(v):
   if v<m or v in used:return
   used.add(v);_,a,b=gs[v-m];visit(a);visit(b)
  visit(end);size=len(used)
  alpha=max(x.bit_count()for x in range(1<<m)if all(not(hood[i]&x)for i in range(m)if x>>i&1));tau=m-alpha;lower=len(es)+tau-1
  if size<lower:
   mp={i:i for i in range(m)};new=[]
   for z,(op,a,b)in enumerate(gs):
    if m+z in used:mp[m+z]=m+len(new);new.append([op,mp[a],mp[b]])
   rec={'source':str(path),'substitution':sub,'n':m,'edges':es,'tau':tau,'gates':new,'output':mp[end],'bound':lower,'full_table_verified':True};(out/'substitution-witness.json').write_text(json.dumps(rec,indent=2));print('WITNESS',rec,flush=True);raise SystemExit
 print(path.name,'tested',checked,'exact C4free',valid,'seconds',round(time.time()-started,2),flush=True)
print('FINISHED',checked,valid,'seconds',round(time.time()-started,2),flush=True)
