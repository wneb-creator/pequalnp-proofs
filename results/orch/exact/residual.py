import argparse,itertools,json,subprocess
from pathlib import Path
from synth import CNF

TRIPLES=[(1,2,3),(0,2,5),(0,3,4),(1,4,5)]
MATCHING=[(0,1),(2,4),(3,5)]
ROWS=[];TARGET=[]
for x in range(128):
 v=[(x>>i)&1 for i in range(7)]
 v.extend(int(any((x>>i)&1 for i in t)) for t in TRIPLES)
 ROWS.append(v)
 TARGET.append(int(any((x>>a)&(x>>b)&1 for a,b in MATCHING) or (v[6] and v[9])))

def encode(m,notcount):
 c=CNF();L=[];R=[];O=[]
 for i in range(m):
  n=11+i;l=[c.var() for _ in range(n)];r=[c.var() for _ in range(n)];o=[c.var() for _ in range(3)]
  L.append(l);R.append(r);O.append(o);c.one(l);c.one(r);c.one(o)
  for a in range(n):
   for b in range(n):
    if a>=b:c.clause(o[2],-l[a],-r[b])
    if a!=b:c.clause(-o[2],-l[a],-r[b])
 if notcount==1:c.one([o[2] for o in O])
 elif notcount==0:
  for o in O:c.clause(-o[2])
 else:c.clause(*(o[2] for o in O))
 for i in range(m-1):c.clause(*(L[j][11+i] for j in range(i+1,m)),*(R[j][11+i] for j in range(i+1,m)))
 for x,vals in enumerate(ROWS):
  V=[c.var() for _ in range(11+m)]
  for k in range(11):c.clause(V[k] if vals[k] else -V[k])
  for i in range(m):
   a=c.var();b=c.var();z=V[11+i]
   for j in range(11+i):
    c.clause(-L[i][j],-a,V[j]);c.clause(-L[i][j],a,-V[j])
    c.clause(-R[i][j],-b,V[j]);c.clause(-R[i][j],b,-V[j])
   opand,opor,opnot=O[i]
   c.clause(-opand,-z,a);c.clause(-opand,-z,b);c.clause(-opand,z,-a,-b)
   c.clause(-opor,z,-a);c.clause(-opor,z,-b);c.clause(-opor,-z,a,b)
   c.clause(-opnot,-z,-a);c.clause(-opnot,z,a)
  c.clause(V[-1] if TARGET[x] else -V[-1])
 return c,L,R,O

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--m',type=int,default=5);ap.add_argument('--notcount',type=int,default=1);ap.add_argument('--seconds',type=int,default=120);ap.add_argument('--dir',required=True);args=ap.parse_args();out=Path(args.dir);out.mkdir(parents=True,exist_ok=True)
 c,L,R,O=encode(args.m,args.notcount);p=out/'formula.cnf';c.write(p);print(f'vars={c.n} clauses={len(c.cl)}',flush=True)
 with (out/'solver.log').open('w') as f:
  try:r=subprocess.run(['/tmp/oec/pequalnp-pilot-98/exact/kissat/build/kissat',f'--time={args.seconds}',str(p)],stdout=f,stderr=subprocess.STDOUT,timeout=args.seconds+30)
  except subprocess.TimeoutExpired:print('timeout',flush=True);return
 print(f'exit={r.returncode}',flush=True)
 if r.returncode!=10:return
 vs=set()
 for line in (out/'solver.log').read_text().splitlines():
  if line.startswith('v '):vs.update(int(z) for z in line.split()[1:] if int(z)>0)
 gs=[]
 for i in range(args.m):
  a=next(j for j,v in enumerate(L[i]) if v in vs);b=next(j for j,v in enumerate(R[i]) if v in vs);op=next(j for j,v in enumerate(O[i]) if v in vs);gs.append(dict(op=['and','or','not'][op],a=a,b=b))
 bad=[]
 for x,vals in enumerate(ROWS):
  v=list(vals)
  for g in gs:
   a=v[g['a']];b=v[g['b']];v.append((a&b) if g['op']=='and' else ((a|b) if g['op']=='or' else 1-a))
  if v[-1]!=TARGET[x]:bad.append(x)
 result=dict(gates=gs,bad=bad);(out/'candidate.json').write_text(json.dumps(result,indent=2));print(json.dumps(result),flush=True)
if __name__=='__main__':main()
