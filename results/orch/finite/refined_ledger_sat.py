import itertools, json, sys
from pathlib import Path
m=int(sys.argv[1]); mode=int(sys.argv[2]); out=Path(sys.argv[3])
p=3; l=4; n=p+l
E=[(0,0),(0,1),(1,1),(1,2),(2,2),(2,0),(0,3)]
tau=3
clauses=[]; nv=0

def new():
 global nv
 nv+=1
 return nv

def neg(a):
 return not a if isinstance(a,bool) else -a

def clause(*args):
 z=[]
 for a in args:
  if a is True: return
  if a is False: continue
  if -a in z: return
  if a not in z: z.append(a)
 clauses.append(z)

def onehot(xs):
 clause(*xs)
 for a,b in itertools.combinations(xs,2): clause(-a,-b)

def iff_and(xs):
 xs=list(xs)
 if False in [x for x in xs if isinstance(x,bool)]: return False
 xs=[x for x in xs if x is not True]
 if not xs: return True
 if len(xs)==1:return xs[0]
 z=new()
 for x in xs:clause(-z,x)
 clause(z,*(neg(x) for x in xs))
 return z

def iff_or(xs):
 return neg(iff_and(neg(x) for x in xs))

ops=[new() for i in range(m)]
pairs=[[(a,b,new()) for a in range(n+i) for b in range(a,n+i)] for i in range(m)]
vals=[[new() for x in range(1<<n)] for i in range(m)]
reaches=[[new() for a in range(n)] for i in range(m)]
outputs=[new() for i in range(m)]
onehot(outputs)

def val(w,x): return bool(x>>w&1) if w<n else vals[w-n][x]
def reach(w,j): return w==j if w<n else reaches[w-n][j]

for i in range(m):
 op=ops[i]
 onehot([s for a,b,s in pairs[i]])
 for a,b,s in pairs[i]:
  for x in range(1<<n):
   av,bv,v=val(a,x),val(b,x),vals[i][x]
   clause(-s,op,-v,av); clause(-s,op,-v,bv); clause(-s,op,v,neg(av),neg(bv))
   clause(-s,-op,v,neg(av)); clause(-s,-op,v,neg(bv)); clause(-s,-op,-v,av,bv)
  for j in range(n):
   av,bv,v=reach(a,j),reach(b,j),reaches[i][j]
   clause(op,-v)
   clause(-s,-op,v,neg(av)); clause(-s,-op,v,neg(bv)); clause(-s,-op,-v,av,bv)
 for a in range(p):
  for b in range(p,n): clause(-reaches[i][a],-reaches[i][b])
 for x in range(1<<n):
  y=any((x>>a&1) and (x>>(p+b)&1) for a,b in E)
  clause(-outputs[i],vals[i][x] if y else -vals[i][x])

neigh=[0]*n
for a,b in E:
 neigh[a]|=1<<(p+b); neigh[p+b]|=1<<a
assert max(x.bit_count() for x in neigh)<=3
specs=[(c,S) for c in range(n) for S in range(1<<n) if S.bit_count()>=2 and S&~neigh[c]==0]
assert len({S for c,S in specs})==len(specs)
exact=[]; family=[]
for i in range(m):
 ex=[]; fa=[]
 for c,S in specs:
  e=iff_and([ops[i]]+[vals[i][x] if x&S else -vals[i][x] for x in range(1<<n)])
  ex.append(e)
  if mode==0: f=e
  else:
   f=iff_and([ops[i],-vals[i][((1<<n)-1)^neigh[c]]]+
       [vals[i][1<<a] if S>>a&1 else -vals[i][1<<a] for a in range(n)])
  fa.append(f)
 exact.append(ex); family.append(fa)

star=[iff_or(family[i]) for i in range(m)]
active=[iff_or(family[i][t] for i in range(m) for t,(cc,S) in enumerate(specs) if cc==c) for c in range(n)]
coverage=[]
for a,b in E:
 ls=[t for t,(c,S) in enumerate(specs) if c==a and S>>(p+b)&1]
 rs=[t for t,(c,S) in enumerate(specs) if c==p+b and S>>a&1]
 coverage += [iff_or(family[i][t] for i in range(m) for t in ls),
              iff_or(family[i][t] for i in range(m) for t in rs)]
 clause(*(exact[i][t] for i in range(m) for t in ls+rs))

# Violation: m-starCount + L + 1 < q + tau + |E|.
# Thus starCount + q + (2|E|-L) >= m-tau+|E|+2.
lits=star+active+[neg(x) for x in coverage]
threshold=m-tau+len(E)+2
dp=[True]+[False]*threshold
for lit in lits:
 old=dp
 dp=[True]+[iff_or([old[k],iff_and([lit,old[k-1]])]) for k in range(1,threshold+1)]
if len(sys.argv)<5 or int(sys.argv[4]): clause(dp[threshold])

out.with_suffix('.cnf').write_text('p cnf %d %d\n'%(nv,len(clauses))+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
out.with_suffix('.json').write_text(json.dumps(dict(m=m,mode=mode,n=n,p=p,E=E,tau=tau,ops=ops,pairs=pairs,vals=vals,reaches=reaches,outputs=outputs,specs=specs,exact=exact,family=family,star=star,active=active,coverage=coverage)))
print('vars',nv,'clauses',len(clauses),'mode',mode,'threshold',threshold,'bytes',out.with_suffix('.cnf').stat().st_size)
