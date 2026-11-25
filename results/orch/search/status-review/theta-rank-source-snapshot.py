from pathlib import Path
import json,sys,time,heapq,itertools
base=Path('/tmp/oec/pequalnp-pilot-65/finite-search');seed=json.loads(Path(sys.argv[1]).read_text());limit=float(sys.argv[2]);width=int(sys.argv[3]);start=time.monotonic()
embedding=[3,0,12,2,8,25,16,13,20,15];theta=seed['gates'];theta_lines={0,2,3,7,12};prefix=[]
def gate(op,a,b):prefix.append((op,a,b));return 26+len(prefix)-1
roots=[]
for line in range(13):
 if line in theta_lines:continue
 xs=[(line+d)%13 for d in [0,1,3,9]];a=xs[0]
 for b in xs[1:]:a=gate('or',a,b)
 roots.append(gate('and',13+line,a))
g=roots[0]
for b in roots[1:]:g=gate('or',g,b)
edges=[(i,j) for i in range(13) for j in range(13) if(i-j)%13 in[0,1,3,9]]
pos=[(1<<i)|(1<<(13+j)) for i,j in edges];neg=json.loads((base/'plane-maxind.json').read_text());rows=[1,1<<13]+pos+neg;target=sum(1<<i for i in range(2,54));badmask=((1<<len(rows))-1)^target
fixed=[(sum(1<<r for r,s in enumerate(rows) if s>>i&1),int(i==13),int(i==0)) for i in range(26)]
def combine(op,a,b):
 av,ax,ay=a;bv,bx,by=b
 if op=='or':return av|bv,ax|bx,ay|by
 return av&bv,(av&1)&bx|ax&(bv&1),((av>>1)&1)&by|ay&((bv>>1)&1)
for op,a,b in prefix:fixed.append(combine(op,fixed[a],fixed[b]))
tags={};line_points={};value_index={v:i for i,v in enumerate(fixed)}
for li,line in enumerate(l for l in range(13) if l not in theta_lines):
 xs=[(line+d)%13 for d in [0,1,3,9]];line_points[line]=frozenset(xs)
 tags[26+4*li]=(line,frozenset(xs[:2]));tags[27+4*li]=(line,frozenset(xs[:3]))
 for size in [2,3]:
  for subset in itertools.combinations(xs,size):
   value=fixed[subset[0]]
   for q in subset[1:]:value=combine('or',value,fixed[q])
   if value in value_index:idx=value_index[value]
   else:idx=len(fixed);fixed.append(value);value_index[value]=idx
   tags[idx]=(line,frozenset(subset))
def requirements(state):
 req={}
 for _,src in state:
  if src in tags:
   line,sub=tags[src];req.setdefault(line,set()).add(sub)
 for subs in req.values():
  if len(subs)>2:return None
  if len(subs)==2:
   a,b=list(subs)
   if not(a<=b or b<=a or a.isdisjoint(b)):return None
 return req
unique={v:i for i,v in reversed(list(enumerate(fixed)))};sources=list(unique.values())

def evaluate(state):
 if requirements(state) is None:return None
 ws=[fixed[i] for i in embedding];ports=[]
 for j,(op,a,b) in enumerate(theta):
  pair=[]
  for p,i in enumerate([a,b]):
   val=ws[i];ports.append(val)
   for key,src in state:
    if key==2*j+p:val=combine('or',val,fixed[src])
   pair.append(val)
  ws.append(combine(op,*pair))
 out=combine('or',fixed[g],ws[seed['output']]);v,dx,dy=out
 if v&badmask or dx or dy:return None
 missing=target&~v
 return missing,tuple(ws[10:]),tuple(ports)
