import itertools,json,sys
from pathlib import Path
source=Path(sys.argv[1]);m=int(sys.argv[2]);kind=sys.argv[3];out=Path(sys.argv[4])
d=json.loads(source.read_text());n=d['n'];p=d['p'];l=n-p;E=list(map(tuple,d['E']));rows=d['rows'];ri={x:i for i,x in enumerate(rows)}
clauses=[];nv=0
def new():
 global nv
 nv+=1;return nv
def neg(x):return not x if isinstance(x,bool) else -x
def clause(*args):
 z=[]
 for a in args:
  if a is True:return
  if a is False:continue
  if -a in z:return
  if a not in z:z.append(a)
 clauses.append(z)
def onehot(xs):
 clause(*xs)
 for a,b in itertools.combinations(xs,2):clause(-a,-b)
def conj(xs):
 xs=list(xs)
 if any(x is False for x in xs):return False
 xs=[x for x in xs if x is not True]
 if not xs:return True
 if len(xs)==1:return xs[0]
 z=new()
 for x in xs:clause(-z,x)
 clause(z,*(neg(x) for x in xs));return z
def disj(xs):return neg(conj(neg(x) for x in xs))
ops=[new() for i in range(m)]
left=[[new() for w in range(n+i)] for i in range(m)]
right=[[new() for w in range(n+i)] for i in range(m)]
vals=[[new() for x in rows] for i in range(m)]
reaches=[[new() for a in range(n)] for i in range(m)]
outputs=[new() for i in range(m)];onehot(outputs)
def val(w,r):return bool(rows[r]>>w&1) if w<n else vals[w-n][r]
def reach(w,a):return w==a if w<n else reaches[w-n][a]
for i in range(m):
 onehot(left[i]);onehot(right[i]);op=ops[i]
 for a in range(n+i):
  for b in range(a):clause(-left[i][a],-right[i][b])
 for r,x in enumerate(rows):
  av,bv=new(),new();v=vals[i][r]
  for w in range(n+i):
   q=val(w,r);aa=left[i][w];bb=right[i][w]
   clause(-aa,-av,q);clause(-aa,av,neg(q));clause(-bb,-bv,q);clause(-bb,bv,neg(q))
  clause(op,-v,av);clause(op,-v,bv);clause(op,v,-av,-bv)
  clause(-op,v,-av);clause(-op,v,-bv);clause(-op,-v,av,bv)
  target=any((x>>a&1) and (x>>(p+b)&1) for a,b in E)
  clause(-outputs[i],v if target else -v)
 for a in range(n):
  av,bv=new(),new();v=reaches[i][a]
  for w in range(n+i):
   q=reach(w,a);aa=left[i][w];bb=right[i][w]
   clause(-aa,-av,q);clause(-aa,av,neg(q));clause(-bb,-bv,q);clause(-bb,bv,neg(q))
  clause(op,-v);clause(-op,v,-av);clause(-op,v,-bv);clause(-op,-v,av,bv)
 for a in range(p):
  for b in range(p,n):clause(-reaches[i][a],-reaches[i][b])
neigh=[0]*n
for a,b in E:neigh[a]|=1<<(p+b);neigh[p+b]|=1<<a
specs=[]
for c,N in enumerate(neigh):
 S=N
 while S:
  if S.bit_count()>=2:specs.append((c,S))
  S=(S-1)&N
exact=[];family=[]
for i in range(m):
 ex=[];fa=[]
 for c,S in specs:
  e=conj([ops[i],-vals[i][ri[((1<<n)-1)^S]]]+[vals[i][ri[1<<a]] for a in range(n) if S>>a&1])
  ex.append(e)
  if kind!='expanded':f=e
  else:f=conj([ops[i],-vals[i][ri[((1<<n)-1)^neigh[c]]]]+[vals[i][ri[1<<a]] if S>>a&1 else -vals[i][ri[1<<a]] for a in range(n)])
  fa.append(f)
 exact.append(ex);family.append(fa)
coverage=[]
for a,b in E:
 ls=[t for t,(c,S) in enumerate(specs) if c==a and S>>(p+b)&1]
 rs=[t for t,(c,S) in enumerate(specs) if c==p+b and S>>a&1]
 clause(*(exact[i][t] for i in range(m) for t in ls+rs))
 coverage.extend([disj(family[i][t] for i in range(m) for t in ls),disj(family[i][t] for i in range(m) for t in rs)])
star=[disj(row) for row in family]
active=[disj(family[i][t] for i in range(m) for t,(cc,S) in enumerate(specs) if cc==c) for c in range(n)]
tau=min(s.bit_count() for s in range(1<<n) if all((s>>a&1) or (s>>(p+b)&1) for a,b in E))
if kind=='full': assert m<len(E)+tau-1
if kind in ['pure','expanded']:
 assert max(N.bit_count() for N in neigh)<=3
 threshold=m-tau+len(E)+2
 dp=[True]+[False]*threshold
 for lit in star+active+[neg(x) for x in coverage]:
  old=dp;dp=[True]+[disj([old[k],conj([lit,old[k-1]])]) for k in range(1,threshold+1)]
 clause(dp[threshold])
assert kind in ['full','pure','expanded','control']
out.with_suffix('.cnf').write_text('p cnf %d %d\n'%(nv,len(clauses))+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
out.with_suffix('.json').write_text(json.dumps(dict(n=n,p=p,m=m,kind=kind,E=E,tau=tau,rows=rows,ops=ops,left=left,right=right,vals=vals,reaches=reaches,outputs=outputs,specs=specs,exact=exact,family=family,star=star,active=active,coverage=coverage)))
print('kind',kind,'n',n,'m',m,'tau',tau,'rows',len(rows),'vars',nv,'clauses',len(clauses),'bytes',out.with_suffix('.cnf').stat().st_size)
