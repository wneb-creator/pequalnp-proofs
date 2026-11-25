# Adapted from results/orch2583/search/fano_cnf.py
# Original SHA256: 61a242834a3002fb168f1958a27a45b1078c7a76b36fc0b705a249b3904cd76c
# Generalized input data, active input count, output directory, and metadata.
# Also adds optional edge-productivity constraints from the agent's productive variant.
import argparse,itertools,json,subprocess,time,hashlib
from pathlib import Path
from datetime import datetime,timezone
P=argparse.ArgumentParser()
P.add_argument('--gates',type=int,required=True)
P.add_argument('--data',required=True)
P.add_argument('--directory',default='/tmp/oec/pequalnp-pilot-103/localblocks')
P.add_argument('--seconds',type=int,default=120)
P.add_argument('--first')
P.add_argument('--pin')
P.add_argument('--mutable')
P.add_argument('--allow-unused',action='store_true')
P.add_argument('--ordered',action='store_true')
P.add_argument('--productive',action='store_true')
P.add_argument('--tag',default='fano')
args=P.parse_args()
root=Path(args.directory);root.mkdir(parents=True,exist_ok=True)
solver=Path('/tmp/oec/pequalnp-pilot-103/setup/lean-4.36.0-linux/bin/cadical')
data=json.loads(Path(args.data).read_text())
E=[tuple(e)for e in data['edges']]
positive=set(data['positive_rows']);negative=set(data['negative_rows']);rows=sorted(positive|negative)
assert len(E)==len(positive) and positive.isdisjoint(negative)
N=args.gates;n=data['inputs']
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
started=datetime.now(timezone.utc).isoformat();start=time.monotonic()
c=CNF();A=[];B=[];O=[]
for i in range(N):
 A.append([c.var()for _ in range(n+i)]);B.append([c.var()for _ in range(n+i)]);O.append(c.var())
 c.one(A[i]);c.one(B[i])
 for a in range(n+i):
  for b in range(a):c.clause(-A[i][a],-B[i][b])
if not args.allow_unused:
 for i in range(N-1):c.clause(*(v for j in range(i+1,N)for v in [A[j][n+i],B[j][n+i]]))
if args.ordered:
 for i in range(N-1):
  for a in range(len(B[i])):
   for b in range(a):c.clause(-B[i][a],-B[i+1][b])
if args.first:
 op,a,b=map(int,args.first.split(','));a,b=sorted((a,b))
 c.clause(O[0]if op==1 else-O[0]);c.clause(A[0][a]);c.clause(B[0][b])
if args.pin:
 pin=json.loads(Path(args.pin).read_text());assert len(pin)==N
 mutable=set(map(int,args.mutable.split(',')))if args.mutable else set()
 for i,(op,a,b)in enumerate(pin):
  if i in mutable:continue
  a,b=sorted((a,b));assert op in[0,1]and a<n+i and b<n+i
  c.clause(O[i]if op else-O[i]);c.clause(A[i][a]);c.clause(B[i][b])
productive=[[]for _ in range(N)]
for x in rows:
 values=[]
 for i in range(N):
  u,v,w=c.var(),c.var(),c.var()
  for src in range(n+i):
   for sels,dest in[(A[i],u),(B[i],v)]:
    if src<n:c.clause(-sels[src],dest if x>>src&1 else-dest)
    else:
     r=values[src-n];c.clause(-sels[src],-dest,r);c.clause(-sels[src],dest,-r)
  o=O[i]
  c.clause(o,-u,-v,w);c.clause(o,u,-w);c.clause(o,v,-w)
  c.clause(-o,u,v,-w);c.clause(-o,-u,w);c.clause(-o,-v,w)
  values.append(w)
  if x in positive:productive[i].append(w)
 c.clause(values[-1]if x in positive else-values[-1])
if args.productive:
 for row in productive:c.clause(*row)
cnf=root/f'{args.tag}.cnf';c.write(cnf)
cnfhash=hashlib.sha256(cnf.read_bytes()).hexdigest()
print('START',started,'gates',N,'first',args.first,'rows',len(rows),'variables',c.nv,'clauses',len(c.cs),'cnf_sha256',cnfhash,flush=True)
outfile=root/f'{args.tag}.stdout';errfile=root/f'{args.tag}.stderr'
with outfile.open('w')as out,errfile.open('w')as err:
 try:r=subprocess.run([str(solver),'-t',str(args.seconds),str(cnf)],stdout=out,stderr=err,timeout=args.seconds+15)
 except subprocess.TimeoutExpired:
  print('RESULT UNKNOWN external timeout',flush=True);raise SystemExit(0)
text=outfile.read_text()
status='SAT'if's SATISFIABLE'in text else'UNSAT'if's UNSATISFIABLE'in text else'UNKNOWN'
result={'started_at':started,'finished_at':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-start,'first':args.first,'gates':N,'inputs':n,'data':args.data,'rows':len(rows),'variables':c.nv,'clauses':len(c.cs),'cnf_sha256':cnfhash,'exit':r.returncode,'status':status,'all_gates_used':not args.allow_unused,'ordered_sources':args.ordered,'productive_on_edge':args.productive}
print('RESULT',json.dumps(result,sort_keys=True),flush=True)
if status=='SAT':
 pos={int(v)for line in text.splitlines()if line.startswith('v ')for v in line.split()[1:]if int(v)>0}
 gates=[(int(O[i]in pos),next(j for j,v in enumerate(A[i])if v in pos),next(j for j,v in enumerate(B[i])if v in pos))for i in range(N)]
 def ev(x):
  w=[bool(x>>j&1)for j in range(n)]
  for op,a,b in gates:w.append((w[a]or w[b])if op else(w[a]and w[b]))
  return w[-1]
 def target(x):return any((x>>a&1)and(x>>b&1)for a,b in E)
 bad=[x for x in range(1<<n)if ev(x)!=target(x)]
 result['full_rows_checked']=1<<n;result['bad_rows']=bad
 print('CANDIDATE',json.dumps(gates),'bad_rows',len(bad),flush=True)
 if not bad:
  (root/f'{args.tag}-witness.json').write_text(json.dumps(gates)+'\n');print('WITNESS',json.dumps(gates),flush=True)
 else:print('INVALID MODEL OR SPECIFICATION',bad,flush=True)
(root/f'{args.tag}-result.json').write_text(json.dumps(result,indent=2)+'\n')
