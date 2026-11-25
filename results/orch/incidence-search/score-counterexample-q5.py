from itertools import product,combinations
from pathlib import Path
import json,time
from datetime import datetime,timezone
start=time.monotonic();prime=5
vectors=[v for v in product(range(prime),repeat=3) if any(v) and next(x for x in v if x)!=0 and next(x for x in v if x)==1]
vectors.sort();p=len(vectors);q=p;n=p+q
edges=[(i,j) for i,a in enumerate(vectors) for j,b in enumerate(vectors) if sum(x*y for x,y in zip(a,b))%prime==0]
neighbors=[[j for a,j in edges if a==i] for i in range(p)]
assert p==31 and len(edges)==186
assert all(len(N)==6 for N in neighbors)
assert all(sum(b==j for a,b in edges)==6 for j in range(q))
assert all(len(set(neighbors[i])&set(neighbors[j]))==1 for i,j in combinations(range(p),2))
match={}
def augment(a,seen):
 for b in neighbors[a]:
  if b in seen:continue
  seen.add(b)
  if b not in match or augment(match[b],seen):match[b]=a;return True
 return False
assert all(augment(a,set()) for a in range(p))
assert len(match)==p
x=0;y=p+neighbors[x][0]
gates=[]
def gate(op,a,b):
 assert a<n+len(gates) and b<n+len(gates)
 gates.append([op,a,b]);return n+len(gates)-1
xb=gate('and',x,x);yb=gate('and',y,y)
shared={}
def anchored_literals(anchor,buffer):
 result=[]
 for z in range(n):
  if z==anchor:result.append(anchor);continue
  key=tuple(sorted((anchor,z)))
  if key not in shared:
   same=(anchor<p)==(z<p)
   shared[key]=gate('or',anchor if same else buffer,z)
  result.append(shared[key])
 return result
xl=anchored_literals(x,xb);yl=anchored_literals(y,yb)
def anchored_dnf(lits):
 terms=[gate('and',lits[a],lits[p+b]) for a,b in edges]
 output=terms[0]
 for t in terms[1:]:output=gate('or',output,t)
 return output
xo=anchored_dnf(xl);yo=anchored_dnf(yl);out=gate('and',xo,yo)
witnesses=[]
for a,N in enumerate(neighbors):
 for j in range(0,len(N),2):
  leaves=[p+N[j],p+N[j+1]]
  w=gate('or',*leaves);witnesses.append(dict(center=a,leaves=leaves,wire=w))
# An antichain of bitsets represents a complete monotone DNF, not sampled inputs.
def minimize(terms):
 result=[]
 for t in sorted(set(terms),key=lambda a:(a.bit_count(),a)):
  if not any(t&u==u for u in result):result.append(t)
 return frozenset(result)
functions=[frozenset([1<<i]) for i in range(n)]
reaches=[1<<i for i in range(n)];supports=[1<<i for i in range(n)]
left=(1<<p)-1;right=((1<<q)-1)<<p
for i,(op,a,b) in enumerate(gates):
 if op=='and':f=minimize(u|v for u in functions[a] for v in functions[b]);reach=0
 else:f=minimize(functions[a]|functions[b]);reach=reaches[a]|reaches[b]
 functions.append(f);reaches.append(reach)
 supports.append(sum(t for t in f if t.bit_count()==1))
 assert not (op=='or' and reach&left and reach&right)
expected=frozenset((1<<a)|(1<<(p+b)) for a,b in edges)
assert functions[out]==expected
assert supports[xo]==1<<x and supports[yo]==1<<y and supports[out]==0
covered=set()
for w in witnesses:
 assert functions[w['wire']]==frozenset(1<<z for z in w['leaves'])
 for z in w['leaves']:
  assert (w['center'],z-p) in edges
  covered.add((w['center'],z-p))
assert covered==set(edges)
R=set();stack=[out]+[w['wire'] for w in witnesses]
while stack:
 w=stack.pop()
 if w<n or w-n in R:continue
 R.add(w-n);_,a,b=gates[w-n];stack.extend([a,b])
B=sum(gates[i][0]=='and' and supports[n+i]==0 and supports[gates[i][1]]!=0 and supports[gates[i][2]]!=0 for i in R)
M=sum(gates[i][0]=='or' and gates[i][1]!=gates[i][2] and supports[gates[i][1]]!=0 and supports[gates[i][2]]!=0 and supports[n+i].bit_count()>1 for i in R)
assert len(gates)==959 and len(R)==959 and B==1 and M==214
assert len(edges)+len(match)==217 and 2*B+M==216
result=dict(p=p,q=q,prime=prime,vectors=vectors,edges=edges,matching=sorted((a,b) for b,a in match.items()),gates=gates,output=out,witnesses=witnesses,anchors=[x,y],B=B,M=M,score=2*B+M,target=len(edges)+len(match))
path=Path('/tmp/oec/pequalnp-pilot-152/score-counterexample-q5.json');path.write_text(json.dumps(result,indent=2))
print(datetime.now(timezone.utc).isoformat(),'PG(2,5) auxiliary score counterexample')
print('vertices',n,'edges',len(edges),'cover_number',len(match),'gates',len(gates),'selected_cone',len(R))
print('B',B,'M',M,'2B+M',2*B+M,'E+tau',len(edges)+len(match))
print('EXACT_DNF_VERIFIED AO2 T0 C4free regular perfect_matching all_star_witnesses')
print('NOT a counterexample to posted gate bound:',len(edges)+len(match),'<=',len(gates)+1)
print('saved',path,'seconds',round(time.monotonic()-start,3))
