import itertools
import json
import sys
from pathlib import Path

n=10
size=int(sys.argv[1])
output=Path(sys.argv[2])
mode=sys.argv[3]
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
edge=edges[0]
samples=[3,6,12,24,17,33,66,132,264,528,160,640,576,320,288,50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
target=[any((m>>a)&1 and (m>>b)&1 for a,b in edges) for m in samples]
clauses=[]; variables=0

def new():
 global variables
 variables+=1
 return variables

def clause(*args): clauses.append(args)

def exactly_one(xs):
 clause(*xs)
 for a,b in itertools.combinations(xs,2): clause(-a,-b)

def equate_if(select,z,value):
 if type(value) is bool:
  clause(-select,z if value else -z)
 else:
  clause(-select,-z,value); clause(-select,z,-value)

def andgate(z,x,y):
 clause(-z,x);clause(-z,y);clause(z,-x,-y)

def orgate(z,x,y):
 clause(z,-x);clause(z,-y);clause(-z,x,y)

left=[];right=[];op=[];out=[];read=[]
for g in range(size):
 av=n+g
 L=[new() for _ in range(av)];R=[new() for _ in range(av)]
 a=new();outs=[new() for _ in samples]
 left.append(L);right.append(R);op.append(a);out.append(outs)
 exactly_one(L);exactly_one(R)
 for i in range(av):
  for j in range(i): clause(-L[i],-R[j])
 for si,m in enumerate(samples):
  u,v=new(),new();w=outs[si]
  for sels,z in [(L,u),(R,v)]:
   for i,sel in enumerate(sels): equate_if(sel,z,bool(m&(1<<i)) if i<n else out[i-n][si])
  clause(-a,-w,u);clause(-a,-w,v);clause(-a,w,-u,-v)
  clause(a,w,-u);clause(a,w,-v);clause(a,-w,u,v)
 rp,rl,rpl=new(),new(),new(); read.append((rp,rl,rpl))
 us=[new() for _ in range(3)];vs=[new() for _ in range(3)]
 for sels,zs in [(L,us),(R,vs)]:
  for i,sel in enumerate(sels):
   vals=(i==edge[0],i==edge[1],False) if i<n else read[i-n]
   for z,val in zip(zs,vals): equate_if(sel,z,val)
 for k,z in [(0,rp),(1,rl)]:
  clause(-a,-z)
  clause(a,z,-us[k]);clause(a,z,-vs[k]);clause(a,-z,us[k],vs[k])
 ab,ba,cross=new(),new(),new();andgate(ab,us[0],vs[1]);andgate(ba,us[1],vs[0]);orgate(cross,ab,ba)
 clause(-a,-rpl,cross);clause(-a,rpl,-cross)
 clause(a,rpl,-us[2]);clause(a,rpl,-vs[2]);clause(a,-rpl,us[2],vs[2])
false=new(); clause(-false)
prev=[-false]+[false]*7
for a in op:
 curr=[-false]+[new() for _ in range(7)]
 for k in range(1,8):
  z=new(); andgate(z,a,prev[k-1]); orgate(curr[k],prev[k],z)
 prev=curr
clause(prev[6]); clause(-prev[7])
for si,t in enumerate(target): clause(out[-1][si] if t else -out[-1][si])
if mode=='nonread': clause(-read[-1][2])
for g in range(size-1): clause(*(sels[h][n+g] for h in range(g+1,size) for sels in [left,right]))
for i in range(n): clause(*(sels[g][i] for g in range(size) for sels in [left,right]))
with output.open('w') as f:
 f.write(f'p cnf {variables} {len(clauses)}\n')
 for cs in clauses: f.write(' '.join(map(str,cs))+' 0\n')
output.with_suffix('.json').write_text(json.dumps(dict(n=n,size=size,edges=edges,edge=edge,left=left,right=right,op=op,out=out,read=read,mode=mode,samples=samples,and_count=6)))
print(variables,len(clauses))
