import argparse,itertools,json,subprocess,time
from pathlib import Path
P=argparse.ArgumentParser()
P.add_argument('--cofactor',action='store_true')
P.add_argument('--gates',type=int,default=19)
P.add_argument('--max-nots',type=int,default=2)
P.add_argument('--seconds',type=int,default=300)
P.add_argument('--ordered',action='store_true')
P.add_argument('--allow-unused',action='store_true')
P.add_argument('--pin')
P.add_argument('--tag',default='cnf')
args=P.parse_args()
root=Path('/tmp/oec/pequalnp-pilot-103/counterexample')
solver=Path('/tmp/oec/pequalnp-pilot-103/setup/lean-4.36.0-linux/bin/cadical')
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
if args.cofactor:E=[(a-1,b-1) for a,b in E if a!=0 and b!=0]
n=9 if args.cofactor else 10
N=args.gates;base=n+1
TOT=1<<n
def target(x):return any((x>>a&1)and(x>>b&1) for a,b in E)
seen={x for x in range(TOT) if x.bit_count()<=2 or x.bit_count()>=n-1 or (not target(x)and all(target(x|(1<<i))for i in range(n) if not x>>i&1))}
class CNF:
 def __init__(self):self.nv=0;self.cs=[]
 def var(self):self.nv+=1;return self.nv
 def clause(self,*xs):self.cs.append(tuple(xs))
 def one(self,xs):
  self.clause(*xs)
  for a,b in itertools.combinations(xs,2):self.clause(-a,-b)
 def write(self,p):
  with p.open('w')as f:
   f.write(f'p cnf {self.nv} {len(self.cs)}\n')
   for c in self.cs:f.write(' '.join(map(str,c))+' 0\n')
print('start',time.time(),'cofactor',args.cofactor,'gates',N,flush=True)
for stage in range(30):
 c=CNF();A=[];B=[];O=[]
 for i in range(N):
  A.append([c.var()for j in range(base+i)]);B.append([c.var()for j in range(base+i)]);O.append([c.var()for j in range(4)])
  c.one(A[i]);c.one(B[i]);c.one(O[i])
  for a in range(base+i):
   for b in range(a):c.clause(-A[i][a],-B[i][b])
  # Unary NOT duplicates its source selector, so the ignored source does not create fake uses.
  for a in range(base+i):
   c.clause(-O[i][2],-A[i][a],B[i][a]);c.clause(-O[i][2],A[i][a],-B[i][a])
  c.clause(-O[i][3],A[i][n]);c.clause(-O[i][3],B[i][n])
 c.clause(*(o[2]for o in O))
 for ns in itertools.combinations([o[2]for o in O],args.max_nots+1):c.clause(*(-v for v in ns))
 if not args.allow_unused:
  for i in range(N-1):c.clause(*(v for j in range(i+1,N) for v in [A[j][base+i],B[j][base+i]]))
 if args.ordered:
  for i in range(N-1):
   for a in range(len(B[i])):
    for b in range(a):c.clause(-B[i][a],-B[i+1][b])
 if args.pin:
  pin=json.loads(Path(args.pin).read_text());assert len(pin)==N
  for i,(o,a,b)in enumerate(pin):
   if o==2:b=a
   elif o==3:a=b=n
   elif a>b:a,b=b,a
   c.clause(O[i][o]);c.clause(A[i][a]);c.clause(B[i][b])
 for x in sorted(seen):
  values=[]
  for i in range(N):
   u,v,w=c.var(),c.var(),c.var()
   for src in range(base+i):
    for sels,dest in [(A[i],u),(B[i],v)]:
     if src<base:
      bit=bool(x>>src&1)if src<n else False
      c.clause(-sels[src],dest if bit else -dest)
     else:
      r=values[src-base]
      c.clause(-sels[src],-dest,r);c.clause(-sels[src],dest,-r)
   oa,oo,on,ot=O[i]
   c.clause(-oa,-u,-v,w);c.clause(-oa,u,-w);c.clause(-oa,v,-w)
   c.clause(-oo,u,v,-w);c.clause(-oo,-u,w);c.clause(-oo,-v,w)
   c.clause(-on,u,w);c.clause(-on,-u,-w)
   c.clause(-ot,w)
   values.append(w)
  c.clause(values[-1]if target(x)else-values[-1])
 path=root/f'{args.tag}-stage{stage}.cnf';c.write(path)
 stdout=root/f'{args.tag}-stage{stage}.stdout';stderr=root/f'{args.tag}-stage{stage}.stderr'
 print('stage',stage,'examples',len(seen),'variables',c.nv,'clauses',len(c.cs),'time',time.time(),flush=True)
 with stdout.open('w')as out,stderr.open('w')as err:
  try:r=subprocess.run([str(solver),'-t',str(args.seconds),str(path)],stdout=out,stderr=err,timeout=args.seconds+15)
  except subprocess.TimeoutExpired:
   print('external timeout',flush=True);break
 text=stdout.read_text()
 status='SAT'if's SATISFIABLE'in text else'UNSAT'if's UNSATISFIABLE'in text else'UNKNOWN'
 print('result',status,'exit',r.returncode,'time',time.time(),flush=True)
 if status!='SAT':break
 positive={int(v)for line in text.splitlines()if line.startswith('v ')for v in line.split()[1:]if int(v)>0}
 gates=[(next(j for j,v in enumerate(O[i])if v in positive),next(j for j,v in enumerate(A[i])if v in positive),next(j for j,v in enumerate(B[i])if v in positive))for i in range(N)]
 def ev(x):
  w=[bool(x>>j&1)for j in range(n)]+[False]
  for op,a,b in gates:w.append((w[a]and w[b])if op==0 else(w[a]or w[b])if op==1 else not w[a]if op==2 else True)
  return w[-1]
 bad=[x for x in range(TOT)if ev(x)!=target(x)]
 print('candidate',gates,'bad',len(bad),flush=True)
 if not bad:
  (root/f'{args.tag}-witness.json').write_text(json.dumps(gates));print('WITNESS',json.dumps(gates),flush=True);break
 new=[]
 for wt in range(n+1):
  for t in [False,True]:new.extend([x for x in bad if x.bit_count()==wt and target(x)==t][:6])
 seen.update(new)
 print('new_examples',new,flush=True)
