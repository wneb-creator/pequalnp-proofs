from itertools import combinations
from pathlib import Path
import json,time
n=9;E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
N=1<<n;full=(1<<N)-1
inp=[sum(1<<x for x in range(N) if x>>i&1) for i in range(n)]
edgeval=sum(1<<x for x in range(N) if any((x>>a)&(x>>b)&1 for a,b in E))
deg=[sum(v in e for e in E) for v in range(n)]
M=[0]+[1<<v for v in range(n)]+[(1<<a)|(1<<b) for a,b in E]
terms={m:sum(1<<x for x in range(N) if x&m==m) for m in M}
edge_rows=sum(1<<((1<<a)|(1<<b)) for a,b in E)
low=[full^i for i in inp]
valid=[((edgeval>>(1<<v))&low[v])&~edgeval for v in range(n)]

def project(g,v):
 lo=g&low[v];return lo|(lo<<(1<<v))
def free(g,bases):
 if g==0:return True
 z=full
 for b in inp+bases:
  if g&~b==0:z&=b
 return z==g
def proof(prefix):
 for v in range(n):
  B=[];good=valid[v]
  for g in prefix:
   pr=project(g,v)
   if not free(pr,B):B.append(pr)
   if pr:good&=~(g^(g>>(1<<v)))&low[v]
  removed=len(prefix)-len(B)
  if removed>=deg[v] or (removed>=deg[v]-1 and good):return True,v
 return False,None
def operands(prefix):
 out=set()
 for m,g in terms.items():
  xs={g}
  for h in prefix:xs|={u&h for u in xs}
  out|={u for u in xs if u&edge_rows}
 return list(out)
first=[]
for a,b in combinations(operands([]),2):
 g=a|b
 if free(g,[]):continue
 first.append(g)
first=list(set(first));badfirst=[];bad2=0;total2=0;start=time.monotonic();examples=[]
for k,g in enumerate(first):
 if proof([g])[0]:continue
 badfirst.append(g);ops=operands([g]);seen=set()
 for a,b in combinations(ops,2):
  h=a|b
  if h in seen or free(h,[g]):continue
  seen.add(h);total2+=1
  if not proof([g,h])[0]:
   bad2+=1
   if len(examples)<12:examples.append([g,h])
 print('first',k,'badfirst',len(badfirst),'bad2',bad2,'total2',total2,'secs',time.monotonic()-start,flush=True)
print('SUMMARY',len(first),len(badfirst),total2,bad2,flush=True)
Path('/tmp/oec/pequalnp-pilot-32/graph_bounds/probe_prefix.json').write_text(json.dumps({'first':len(first),'badfirst':len(badfirst),'total2':total2,'bad2':bad2,'examples':examples},indent=2))
