import itertools,json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-31/random/near_one');out=Path('/tmp/oec/pequalnp-pilot-31/search');checked=0;valid=0
for path in sorted(base.glob('near-8-*.json')):
 d=json.loads(path.read_text());n=d['n'];gates=d['gates']
 for state in itertools.product([-1,0,1],repeat=n):
  m=state.count(-1)
  if m<2 or m==n:continue
  full=(1<<(1<<m))-1;inputs=[sum(1<<x for x in range(1<<m)if x>>i&1)for i in range(m)];vals={-2:full,-1:0,**dict(enumerate(inputs))};byfun={v:k for k,v in vals.items()};ws=[];q=0;gs=[]
  for s in state:
   if s==-1:ws.append(q);q+=1
   else:ws.append(-2 if s else -1)
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
  checked+=1;used=set()
  def visit(v):
   if v<m or v in used:return
   used.add(v);_,a,b=gs[v-m];visit(a);visit(b)
  visit(end);size=len(used)
  alpha=max(x.bit_count()for x in range(1<<m)if all(not(hood[i]&x)for i in range(m)if x>>i&1));tau=m-alpha;lower=len(es)+tau-1;valid+=1
  if size<lower:
   mp={i:i for i in range(m)};new=[]
   for z,(op,a,b)in enumerate(gs):
    if m+z in used:mp[m+z]=m+len(new);new.append([op,mp[a],mp[b]])
   rec={'source':str(path),'restriction':state,'n':m,'edges':es,'tau':tau,'gates':new,'output':mp[end],'bound':lower,'full_table_verified':True};(out/'restriction-witness.json').write_text(json.dumps(rec,indent=2));print('WITNESS',rec,flush=True);raise SystemExit
 print(path.name,'exact C4free restrictions',checked,flush=True)
print('FINISHED',checked,valid,flush=True)
