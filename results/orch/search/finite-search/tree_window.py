from pathlib import Path
import json,sys
base=Path('/tmp/oec/pequalnp-pilot-65/finite-search');crosscount=int(sys.argv[1]);dest=Path(sys.argv[2]);prefix=[];roots=[];cross={}
def gate(op,a,b):prefix.append((op,a,b));return 26+len(prefix)-1
for line in range(13):
 if line in [0,2,3,7]:continue
 xs=[(line+d)%13 for d in [0,1,3,9]];a=next(x for x in xs if x in [0,1,9]);b=next(x for x in xs if x in [7,8,10]);pair=gate('or',a,b);cross[(a,b)]=pair;root=pair
 for q in xs:
  if q not in [a,b]:root=gate('or',root,q)
 roots.append(gate('and',13+line,root))
for line,points in [(2,[2,5,11]),(3,[4,6,12])]:
 root=points[0]
 for q in points[1:]:root=gate('or',root,q)
 roots.append(gate('and',13+line,root))
f=roots[0]
for root in roots[1:]:f=gate('or',f,root)
assert len(prefix)==52
raw=[3,0,1,9,7,8,10,13,15,16,20]
preds=raw[:]
if crosscount==3:preds += [cross[p] for p in [(0,7),(1,8),(9,10)]]
if crosscount==9:preds += list(cross.values())
def eval(s):
 w=[int(s>>i&1) for i in range(26)]
 for op,a,b in prefix:w.append(w[a]|w[b] if op=='or' else w[a]&w[b])
 return w
def deriv(s,var):
 w=eval(s);d=[int(i==var) for i in range(26)]
 for op,a,b in prefix:d.append(d[a]|d[b] if op=='or' else(w[a]&d[b])|(d[a]&w[b]))
 return d
dx=deriv(1,13);dy=deriv(1<<13,0)
edges=[(i,j) for i in range(13) for j in range(13) if(i-j)%13 in[0,1,3,9]];pos=[(1<<i)|(1<<(13+j)) for i,j in edges];pos=[s for s in pos if not eval(s)[f]];assert len(pos)==10
neg=json.loads((base/'plane-maxind.json').read_text());patterns={}
for s,target in [(1,0),(1<<13,0)]+[(s,1) for s in pos]+[(s,0) for s in neg]:
 w=eval(s);pat=tuple(w[i] for i in preds)
 if pat in patterns:assert patterns[pat]==target
 patterns[pat]=target
basekeys=[tuple(eval(s)[i] for i in preds) for s in [1,1<<13]]
def le(a,b):return all(x<=y for x,y in zip(a,b))
rows=[r for r,t in patterns.items() if r in basekeys or not any(r!=q and t==u and (le(q,r) if t else le(r,q)) for q,u in patterns.items())]
report={'preds':preds,'window_budget':11,'values':rows,'targets':[patterns[r] for r in rows],'dx':[dx[i] for i in preds],'dy':[dy[i] for i in preds],'base_channels':[rows.index(r) for r in basekeys],'prefix':prefix,'final_or_with':f,'crosscount':crosscount}
dest.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'prefix':len(prefix),'new_gates':11,'final_or':1,'rows':len(rows),'predecessors':len(preds)}))
