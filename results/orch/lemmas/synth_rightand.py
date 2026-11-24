import subprocess,time,json
from pathlib import Path
from itertools import combinations
p=Path('/tmp/oec/pequalnp-pilot-48')
solver=p/'elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
n=14;k=20
lines=sorted({tuple(sorted((a,b,a^b))) for a,b in combinations(range(1,8),2)})
edges=[(a-1,7+j) for a in range(1,8) for j,L in enumerate(lines) if a in L]
def target(s):return any(s>>a&1 and s>>b&1 for a,b in edges)
rows={s for s in range(1<<n) if s&127 and s.bit_count()<=2}
rows.add(((1<<7)-1)<<7)
start=time.monotonic()
for turn in range(2):
 nv=0;cs=[]
 def var():
  global nv
  nv+=1;return nv
 def add(*a):cs.append(a)
 def one(a):
  add(*a)
  for i,j in combinations(a,2):add(-i,-j)
 left=[];right=[];ops=[]
 for i in range(k):
  l=[var() for _ in range(n+i)];r=[var() for _ in range(n+i)];o=var()
  left.append(l);right.append(r);ops.append(o);one(l);one(r)
  for a in range(n+i):
   for b in range(a+1):add(-l[a],-r[b])
 for i in range(k-1):
  add(*(left[j][n+i] for j in range(i+1,k)),*(right[j][n+i] for j in range(i+1,k)))
 add(ops[-1]);add(ops[-2]);add(right[-1][n+k-2]);add(left[0][7]);add(right[0][8]);add(ops[0])
 for s in sorted(rows):
  ys=[]
  for i in range(k):
   a=var();b=var();y=var();ys.append(y)
   for sels,d in [(left[i],a),(right[i],b)]:
    for src,sel in enumerate(sels):
     if src<n:add(-sel,d if s>>src&1 else -d)
     else:
      z=ys[src-n];add(-sel,-d,z);add(-sel,d,-z)
   o=ops[i]
   add(-o,-a,-b,y);add(-o,a,-y);add(-o,b,-y)
   add(o,a,b,-y);add(o,-a,y);add(o,-b,y)
  want=target(s) if s&127 else True
  add(ys[-1] if want else -ys[-1])
 cnf=p/f'heawood-rightand-{turn}.cnf'
 with cnf.open('w') as f:
  f.write(f'p cnf {nv} {len(cs)}\n')
  for c in cs:f.write(' '.join(map(str,c))+' 0\n')
 log=p/f'heawood-rightand-{turn}.log'
 print('turn',turn,'tests',len(rows),'vars',nv,'clauses',len(cs),flush=True)
 remain=350-(time.monotonic()-start)
 if remain<=1:break
 with log.open('w') as f:
  r=subprocess.run([str(solver),'-t',str(min(70,int(remain))),str(cnf)],stdout=f,stderr=subprocess.STDOUT)
 print('solver_exit',r.returncode,'elapsed',round(time.monotonic()-start,1),flush=True)
 if r.returncode!=10:
  print('No model found; status is UNSAT only if solver_exit=20, otherwise unknown.',flush=True)
  break
 model=set()
 for line in log.read_text().splitlines():
  if line.startswith('v '):model.update(int(x) for x in line[2:].split() if int(x)>0)
 gates=[]
 for i in range(k):
  a=next(j for j,v in enumerate(left[i]) if v in model)
  b=next(j for j,v in enumerate(right[i]) if v in model)
  gates.append(('and' if ops[i] in model else 'or',a,b))
 def evaluate(s):
  w=[bool(s>>j&1) for j in range(n)]
  for op,a,b in gates:w.append(w[a]&w[b] if op=='and' else w[a]|w[b])
  return w[-1]
 bad=[s for s in range(1<<n) if s&127 and evaluate(s)!=target(s)]
 (p/f'heawood-rightand-{turn}-candidate.json').write_text(json.dumps({'gates':gates,'bad_count':len(bad)}))
 print('counterexamples',len(bad),flush=True)
 if not bad:
  print('FOUND exact20-gate extension',gates,flush=True)
  break
 rows.update(sorted(bad,key=lambda s:(s.bit_count(),s))[:12])
print('total_seconds',round(time.monotonic()-start,1),flush=True)
