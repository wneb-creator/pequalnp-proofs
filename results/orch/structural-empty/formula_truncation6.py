import itertools,json,time
from pathlib import Path
out=Path('/tmp/oec/pequalnp-pilot-87/counterexample/structural-empty')
n=6;inputs=[sum(1<<r for r in range(1<<n)if r>>i&1)for i in range(n)]
seen={v:1 for v in inputs};expr={v:i for i,v in enumerate(inputs)};buckets=[[],inputs]
pairrows=[(i,j,(1<<i)|(1<<j))for i in range(n)for j in range(i+1,n)]
edgefn={(i,j):inputs[i]&inputs[j]for i,j,r in pairrows}
start=time.monotonic();found=[]
def formula(v):
 e=expr[v]
 if isinstance(e,int):return e
 return [e[0],formula(e[1]),formula(e[2])]
for leaves in range(2,9):
 cur=[]
 for k in range(1,leaves//2+1):
  l=leaves-k
  if l>=len(buckets):continue
  for a in buckets[k]:
   for b in buckets[l]:
    if k==l and a>b:continue
    for op,v in [('and',a&b),('or',a|b)]:
     if v not in seen:seen[v]=leaves;expr[v]=(op,a,b);cur.append(v)
 buckets.append(cur)
 print(json.dumps({'leaves':leaves,'new':len(cur),'total':len(seen),'seconds':time.monotonic()-start}),flush=True)
 for f in cur:
  if any(f>>(1<<i)&1 for i in range(n)):continue
  edges=[(i,j)for i,j,r in pairrows if f>>r&1]
  q=0
  for e in edges:q|=edgefn[e]
  if not q or q==f:continue
  if q not in seen:
   triangles=any(all(tuple(sorted(e))in edges for e in [(a,b),(a,c),(b,c)])for a,b,c in itertools.combinations(range(n),3))
   c4=any(all(tuple(sorted(e))in edges for e in [(a,b),(b,c),(c,d),(d,a)])for a,b,c,d in itertools.permutations(range(n),4))
   row={'leaves_f':leaves,'f':hex(f),'q':hex(q),'expr':formula(f),'edges':edges,'triangle_free':not triangles,'c4_free':not c4}
   found.append(row);print('TRUNCATION_INCREASE',json.dumps(row),flush=True)
 if found:break
 if False:break
out.joinpath('truncation6-results.json').write_text(json.dumps({'found':found,'functions':len(seen),'maximum_leaf_level':len(buckets)-1,'seconds':time.monotonic()-start},indent=2))
