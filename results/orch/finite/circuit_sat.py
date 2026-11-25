import itertools,json,sys
from pathlib import Path
m=int(sys.argv[1]); max_or=int(sys.argv[2]); tzero=int(sys.argv[3]); n=6;p=3
out=Path(sys.argv[4]); clauses=[]; nv=0
def new():
 global nv
 nv+=1;return nv
def clause(*args):
 z=[]
 for a in args:
  if a is True:return
  if a is False:continue
  if -a in z:return
  if a not in z:z.append(a)
 clauses.append(z)
def neg(x):return not x if isinstance(x,bool) else -x
ops=[new() for i in range(m)]
pairs=[[(a,b,new()) for a in range(n+i) for b in range(a,n+i)] for i in range(m)]
vals=[[new() for x in range(1<<n)] for i in range(m)]
reaches=[[new() for j in range(n)] for i in range(m)] if tzero else []
def val(w,x):return bool(x>>w&1) if w<n else vals[w-n][x]
def reach(w,j):return w==j if w<n else reaches[w-n][j]
for i in range(m):
 op=ops[i];ps=pairs[i]
 clause(*(s for a,b,s in ps))
 for (_,_,s),(_,_,t) in itertools.combinations(ps,2):clause(-s,-t)
 for a,b,s in ps:
  if a==b:clause(-s,-op)
  for x in range(1<<n):
   av,bv,v=val(a,x),val(b,x),vals[i][x]
   clause(-s,op,-v,av);clause(-s,op,-v,bv);clause(-s,op,v,neg(av),neg(bv))
   clause(-s,-op,v,neg(av));clause(-s,-op,v,neg(bv));clause(-s,-op,-v,av,bv)
  if tzero:
   for j in range(n):
    av,bv,v=reach(a,j),reach(b,j),reaches[i][j]
    clause(op,-v)
    clause(-s,-op,v,neg(av));clause(-s,-op,v,neg(bv));clause(-s,-op,-v,av,bv)
 if tzero:
  for a in range(p):
   for b in range(p,n):clause(-reaches[i][a],-reaches[i][b])
for i in range(m-1):clause(*(s for j in range(i+1,m) for a,b,s in pairs[j] if a==n+i or b==n+i))
if max_or<m:
 for oo in itertools.combinations(ops,max_or+1):clause(*(-o for o in oo))
E=[(0,0),(0,1),(1,1),(1,2),(2,2),(2,0)]
for x in range(1<<n):
 y=any((x>>a&1) and (x>>(p+b)&1) for a,b in E)
 clause(vals[-1][x] if y else -vals[-1][x])
out.with_suffix('.cnf').write_text('p cnf %d %d\n'%(nv,len(clauses))+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
out.with_suffix('.json').write_text(json.dumps(dict(m=m,max_or=max_or,tzero=tzero,n=n,p=p,E=E,ops=ops,pairs=pairs,vals=vals,reaches=reaches)))
print('CNF vars',nv,'clauses',len(clauses),'bytes',out.with_suffix('.cnf').stat().st_size)
