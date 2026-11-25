import argparse,itertools,json,subprocess,time
from pathlib import Path
from synth import CNF

N=6
# Inputs in order 0,1,3,7,8,9 of Petersen.
TRIPLES=[(1,2,3),(0,2,5),(0,3,4),(1,4,5)]
MATCHING=[(0,1),(2,4),(3,5)]
TARGETS=[[int(any((x>>i)&1 for i in t)) for x in range(64)] for t in TRIPLES]+[[int(any((x>>a)&(x>>b)&1 for a,b in MATCHING)) for x in range(64)]]

def encode(m,notcount,first=-1):
 c=CNF();L=[];R=[];O=[];S=[]
 for i in range(m):
  n=N+i;l=[c.var() for _ in range(n)];r=[c.var() for _ in range(n)];o=[c.var() for _ in range(3)]
  L.append(l);R.append(r);O.append(o);c.one(l);c.one(r);c.one(o)
  for a in range(n):
   for b in range(n):
    if a>=b:c.clause(o[2],-l[a],-r[b])
    if a!=b:c.clause(-o[2],-l[a],-r[b])
 if notcount==1:c.one([o[2] for o in O])
 elif notcount==0:
  for o in O:c.clause(-o[2])
 elif notcount>1:
  ns=[o[2] for o in O]
  for xs in itertools.combinations(ns,notcount+1):c.clause(*(-x for x in xs))
  for xs in itertools.combinations(ns,m-notcount+1):c.clause(*xs)
 else:c.clause(*(o[2] for o in O))
 if first>=0:
  if first==4:c.clause(O[0][2]);c.clause(L[0][0]);c.clause(R[0][0])
  else:
   c.clause(O[0][first//2]);c.clause(L[0][0]);c.clause(R[0][1+(first%2)])
 for t in range(5):
  s=[c.var() for _ in range(m)];S.append(s);c.one(s)
  if notcount==1:
   for i in range(m):c.clause(-s[i],-O[i][2])
 # All gates must feed a gate or designated output.
 for i in range(m):c.clause(*(L[j][N+i] for j in range(i+1,m)),*(R[j][N+i] for j in range(i+1,m)),*(s[i] for s in S))
 for x in range(64):
  if x.bit_count()>1 and x not in (3,20,40):continue
  V=[c.var() for _ in range(N+m)]
  for k in range(N):c.clause(V[k] if (x>>k)&1 else -V[k])
  for i in range(m):
   a=c.var();b=c.var();z=V[N+i]
   for j in range(N+i):
    c.clause(-L[i][j],-a,V[j]);c.clause(-L[i][j],a,-V[j])
    c.clause(-R[i][j],-b,V[j]);c.clause(-R[i][j],b,-V[j])
   opand,opor,opnot=O[i]
   c.clause(-opand,-z,a);c.clause(-opand,-z,b);c.clause(-opand,z,-a,-b)
   c.clause(-opor,z,-a);c.clause(-opor,z,-b);c.clause(-opor,-z,a,b)
   c.clause(-opnot,-z,-a);c.clause(-opnot,z,a)
  for t in range(5):
   if t<4 and TARGETS[4][x]:continue
   for i in range(m):c.clause(-S[t][i],V[N+i] if TARGETS[t][x] else -V[N+i])
 return c,L,R,O,S

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--m',type=int,default=11);ap.add_argument('--first',type=int,default=-1);ap.add_argument('--notcount',type=int,default=1);ap.add_argument('--seconds',type=int,default=180);ap.add_argument('--seed',type=int,default=98);ap.add_argument('--dir',required=True);args=ap.parse_args();out=Path(args.dir);out.mkdir(parents=True,exist_ok=True)
 c,L,R,O,S=encode(args.m,args.notcount,args.first);p=out/'formula.cnf';c.write(p);print(f'vars={c.n} clauses={len(c.cl)}',flush=True)
 with (out/'solver.log').open('w') as f:
  try:r=subprocess.run(['/tmp/oec/pequalnp-pilot-98/exact/kissat/build/kissat',f'--time={args.seconds}',f'--seed={args.seed}',str(p)],stdout=f,stderr=subprocess.STDOUT,timeout=args.seconds+30)
  except subprocess.TimeoutExpired:print('timeout',flush=True);return
 print(f'exit={r.returncode}',flush=True)
 if r.returncode!=10:return
 vs=set()
 for line in (out/'solver.log').read_text().splitlines():
  if line.startswith('v '):vs.update(int(z) for z in line.split()[1:] if int(z)>0)
 gs=[]
 for i in range(args.m):
  a=next(j for j,v in enumerate(L[i]) if v in vs);b=next(j for j,v in enumerate(R[i]) if v in vs);op=next(j for j,v in enumerate(O[i]) if v in vs);gs.append(dict(op=['and','or','not'][op],a=a,b=b))
 outputs=[N+next(i for i,v in enumerate(s) if v in vs) for s in S]
 bad=[]
 for x in range(64):
  if x.bit_count()>1 and x not in (3,20,40):continue
  v=[(x>>i)&1 for i in range(N)]
  for g in gs:
   a=v[g['a']];b=v[g['b']];v.append((a&b) if g['op']=='and' else ((a|b) if g['op']=='or' else 1-a))
  if any((t==4 or not TARGETS[4][x]) and v[o]!=TARGETS[t][x] for t,o in enumerate(outputs)):bad.append(x)
 result=dict(gates=gs,outputs=outputs,bad=bad);(out/'candidate.json').write_text(json.dumps(result,indent=2));print(json.dumps(result),flush=True)
if __name__=='__main__':main()
