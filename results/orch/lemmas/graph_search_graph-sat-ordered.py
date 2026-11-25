import json,sys
from pathlib import Path
G=int(sys.argv[1]) if len(sys.argv)>1 else 13
mode=sys.argv[2] if len(sys.argv)>2 else 'one_not'
root=Path('/tmp/oec/pequalnp-pilot-182')
clauses=[];num=0

def var():
 global num
 num+=1
 return num

def add(*xs):
 a=[]
 for x in xs:
  if x is True:return
  if x is False:continue
  a.append(x)
 clauses.append(a)

def neg(x):return not x if isinstance(x,bool) else -x

def exactly(xs):
 add(*xs)
 for i,x in enumerate(xs):
  for y in xs[:i]:add(-x,-y)

ops=[[var() for _ in range(3)] for i in range(G)]
sel=[[[var() for j in range(7+i)] for k in range(2)] for i in range(G)]
v=[[var() for row in range(128)] for i in range(G)]
a=[[var() for row in range(128)] for i in range(G)]
b=[[var() for row in range(128)] for i in range(G)]
for i in range(G):
 exactly(ops[i])
 if mode=='mono':add(-ops[i][2])
 else:
  for j in range(i):add(-ops[i][2],-ops[j][2])
 for side in sel[i]:exactly(side)
 # Normalize commutative input order; keep NOT's unused second input zero.
 for x in range(7+i):
  for y in range(x):add(ops[i][2],-sel[i][0][x],-sel[i][1][y])
 for j in range(1,7+i):add(-ops[i][2],-sel[i][1][j])
 for row in range(128):
  for side,sv in [(0,a[i][row]),(1,b[i][row])]:
   for j,q in enumerate(sel[i][side]):
    w=bool(row>>j&1) if j<7 else v[j-7][row]
    add(-q,-sv,w);add(-q,sv,neg(w))
  x,y,z=a[i][row],b[i][row],v[i][row]
  q=ops[i][0]
  add(-q,-z,x);add(-q,-z,y);add(-q,z,-x,-y)
  q=ops[i][1]
  add(-q,z,-x);add(-q,z,-y);add(-q,-z,x,y)
  q=ops[i][2]
  add(-q,-z,-x);add(-q,z,x)
# Every gate is used; identities allow padding smaller circuits.
for i in range(G-1):
 add(*[sel[j][side][7+i] for j in range(i+1,G) for side in range(2)])
for x in range(7):add(*[sel[i][side][x] for i in range(G) for side in range(2)])
# Canonical topological order by maximum predecessor index.
for i in range(G-1):
 for p in range(7+i):
  for q in range(p):
   ni,nj=ops[i][2],ops[i+1][2]
   add(ni,nj,-sel[i][1][p],-sel[i+1][1][q])
   add(-ni,nj,-sel[i][0][p],-sel[i+1][1][q])
   add(ni,-nj,-sel[i][1][p],-sel[i+1][0][q])
E=[(0,2),(1,3),(0,4),(1,4),(2,4),(0,5),(1,5),(3,5),(0,6),(2,6),(3,6),(5,6)]
for row in range(128):
 target=any((row>>x&1) and (row>>y&1) for x,y in E)
 add(v[-1][row] if target else -v[-1][row])
name=f'graph-{G}-{mode}-ordered'
(root/(name+'.cnf')).write_text(f'p cnf {num} {len(clauses)}\n'+'\n'.join(' '.join(map(str,c))+' 0' for c in clauses)+'\n')
(root/(name+'.mapping.json')).write_text(json.dumps({'gates':G,'mode':mode,'ops':ops,'sel':sel,'out':v}))
print(name,'variables',num,'clauses',len(clauses))
