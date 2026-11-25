import json,subprocess,sys,time,itertools
from pathlib import Path
P=Path('/tmp/oec/pequalnp-pilot-131')
SOLVER=P/'elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def aim(x):return any((x>>a&1) and (x>>b&1) for a,b in E)
n=int(sys.argv[1]) if len(sys.argv)>1 else 19
seconds=int(sys.argv[2]) if len(sys.argv)>2 else 600
mode=sys.argv[3] if len(sys.argv)>3 else 'one'
name=f'sat-{n}-{mode}'
samples=sorted({x for x in range(1024) if not aim(x)}|{(1<<a)|(1<<b) for a,b in E}|{1023})
start=time.monotonic()
for iteration in range(30):
 clauses=[];nv=0
 def var():
  global nv
  nv+=1;return nv
 def clause(*v):clauses.append(list(v))
 def one(vs):
  clause(*vs)
  for a,b in itertools.combinations(vs,2):clause(-a,-b)
 ops=[];sel=[]
 for j in range(n):
  o=[var() for k in range(3)];one(o);ops.append(o)
  a=[var() for k in range(10+j)];b=[var() for k in range(10+j)];one(a);one(b);sel.append((a,b))
  for u in range(10+j):
   for v in range(u):clause(o[2],-a[u],-b[v])
  for u in range(10+j):
   clause(-o[2],-a[u],b[u])
 # Last gate cannot be NOT in a one-NOT circuit computing nonconstant monotone f.
 if mode=='one':
  one([o[2] for o in ops]);clause(-ops[-1][2])
 elif mode=='mono':
  for o in ops:clause(-o[2])
 else:clause(*(o[2] for o in ops))
 # Every gate other than the output is consumed, for lean minimal witnesses.
 for j in range(n-1):clause(*(sel[k][side][10+j] for k in range(j+1,n) for side in range(2)))
 # Automorphisms normalize the first gate to input 0 and edge or nonedge input.
 clause(sel[0][0][0]);clause(sel[0][1][0],sel[0][1][1],sel[0][1][2])
 clause(-sel[0][1][0],ops[0][2])
 for j,(o,a,b) in enumerate(json.loads((P/'upper-gates.json').read_text())):
  clause(ops[j][o]);clause(sel[j][0][a]);clause(sel[j][1][b])
 for x in samples:
  values=[]
  for j in range(n):
   av,bv,v=var(),var(),var();values.append(v)
   for side,sv in enumerate((av,bv)):
    for k,s in enumerate(sel[j][side]):
     if k<10:clause(-s,sv if x>>k&1 else -sv)
     else:
      source=values[k-10];clause(-s,-sv,source);clause(-s,sv,-source)
   oa,oo,on=ops[j]
   clause(-oa,-av,-bv,v);clause(-oa,av,-v);clause(-oa,bv,-v)
   clause(-oo,av,bv,-v);clause(-oo,-av,v);clause(-oo,-bv,v)
   clause(-on,av,v);clause(-on,-av,-v)
  clause(values[-1] if aim(x) else -values[-1])
 cnf=P/(name+'.cnf')
 with cnf.open('w') as f:
  f.write(f'p cnf {nv} {len(clauses)}\n')
  for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
 remaining=int(seconds-(time.monotonic()-start))
 if remaining<=0:break
 out=P/(name+f'-{iteration}.out');err=P/(name+f'-{iteration}.err')
 print('iteration',iteration,'rows',len(samples),'vars',nv,'clauses',len(clauses),'remaining',remaining,flush=True)
 with out.open('w') as fo,err.open('w') as fe:
  cp=subprocess.run([str(SOLVER),'-t',str(remaining),'--seed=2592',str(cnf)],stdout=fo,stderr=fe)
 print('solver exit',cp.returncode,flush=True)
 if cp.returncode!=10:break
 trues=set()
 for line in out.read_text().splitlines():
  if line.startswith('v '):trues.update(int(t) for t in line[2:].split() if int(t)>0)
 g=[]
 for j in range(n):g.append((next(i for i,v in enumerate(ops[j]) if v in trues),*(next(i for i,v in enumerate(side) if v in trues) for side in sel[j])))
 def ev(x):
  v=[bool(x>>k&1) for k in range(10)]
  for o,a,b in g:v.append(v[a] and v[b] if o==0 else v[a] or v[b] if o==1 else not v[a])
  return v[-1]
 bad=[x for x in range(1024) if ev(x)!=aim(x)]
 print('full-table bad',len(bad),'gates',g,flush=True)
 (P/(name+'-candidate.json')).write_text(json.dumps({'gates':g,'errors':bad,'samples':samples}))
 if not bad:
  print('WITNESS',flush=True);break
 samples=sorted(set(samples)|set(bad[:40]))
