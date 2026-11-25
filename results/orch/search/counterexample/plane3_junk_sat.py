import json,random,time,subprocess,itertools,sys
from pathlib import Path
P=Path('/tmp/oec/pequalnp-pilot-131');SOLVER=P/'elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
data=json.loads((P/'plane3-search-data.json').read_text());E=data['edges'];N=26
seed=int(sys.argv[1]) if len(sys.argv)>1 else 25831
seconds=int(sys.argv[2]) if len(sys.argv)>2 else 1200
rng=random.Random(seed);case=seed%2
last=[0,1,3] if case==0 else [0,1,2]
vs=[v for v in range(13) if v not in last];rng.shuffle(vs);vs+=last
g=[];stars=[]
for p in vs:
 ns=[b for a,b in E if a==p];rng.shuffle(ns);w=ns[0]
 for b in ns[1:]:g.append((1,w,b));w=N+len(g)-1
 g.append((0,p,w));stars.append(N+len(g)-1)
w=stars[0]
for b in stars[1:]:g.append((1,w,b));w=N+len(g)-1
assert len(g)==64
remove=40;replacement=g[remove][1]
g.pop(remove)
def remap(w):return replacement if w==N+remove else w-1 if w>N+remove else w
g=[(o,remap(a),remap(b)) for o,a,b in g]
mutable=set(range(40,51))|{61,62}
name=f'plane3-junk-{seed}'
(P/(name+'-seed.json')).write_text(json.dumps({'gates':g,'mutable':sorted(mutable),'point_order':vs}))
neg=data['maximal_false'];samples=sorted(data['minimal_true']+[m for m in neg if m.bit_count()>=10]+rng.sample([m for m in neg if m.bit_count()<10],32))
start=time.monotonic()
for iteration in range(30):
 clauses=[];nv=0
 def var():
  global nv
  nv+=1;return nv
 def inv(x):return not x if isinstance(x,bool) else -x
 def clause(*ls):
  lits=set()
  for x in ls:
   if x is True:return
   if x is False:continue
   if -x in lits:return
   lits.add(x)
  clauses.append(sorted(lits))
 def one(xs):
  clause(*xs)
  for a,b in itertools.combinations(xs,2):clause(-a,-b)
 controls={}
 for j in sorted(mutable):
  o=var();a=[var() for k in range(N+j)];b=[var() for k in range(N+j)];one(a);one(b)
  for u in range(N+j):
   for v in range(u+1):clause(-a[u],-b[v])
  controls[j]=(o,a,b)
 for j in range(len(g)-1):
  if any(k not in mutable and (N+j in g[k][1:]) for k in range(j+1,len(g))):continue
  users=[]
  for k,(o,a,b) in controls.items():
   if k>j:users.extend([a[N+j],b[N+j]])
  clause(*users)
 junk={j:var() for j in mutable}
 clause(*junk.values())
 for j,t in junk.items():clause(-t,-controls[j][0])
 fixed_and=sum(o==0 for j,(o,a,b) in enumerate(g) if j not in mutable)
 needed=13-fixed_and
 if needed>0:
  for subset in itertools.combinations([o for o,a,b in controls.values()],len(controls)-needed+1):clause(*(-o for o in subset))
 def gate(o,a,b):
  if isinstance(o,bool):
   if isinstance(a,bool) and isinstance(b,bool):return (a or b) if o else (a and b)
   if a is True:return True if o else b
   if b is True:return True if o else a
   if a is False:return b if o else False
   if b is False:return a if o else False
   if a==b:return a
  v=var()
  clause(o,inv(a),inv(b),v);clause(o,a,-v);clause(o,b,-v)
  clause(inv(o),a,b,-v);clause(inv(o),inv(a),v);clause(inv(o),inv(b),v)
  return v
 for x in samples+[-1,-2,-3]:
  values=[var() for i in range(N)] if x<0 else [bool(x>>i&1) for i in range(N)]
  if x==-1:
   for a,b in E:clause(-values[a],-values[b])
  for j,(op,aa,bb) in enumerate(g):
   if j in mutable:
    o,a,b=controls[j];av,bv=var(),var()
    for sels,vv in [(a,av),(b,bv)]:
     for k,s in enumerate(sels):
      w=values[k];clause(-s,-vv,w);clause(-s,vv,inv(w))
    value=gate(o,av,bv)
    if x==-1:clause(-junk[j],value)
    if x==-2:clause(-junk[j],av);clause(-junk[j],-bv)
    if x==-3:clause(-junk[j],-av);clause(-junk[j],bv)
   else:value=gate(bool(op),values[aa],values[bb])
   values.append(value)
  if x>=-1:clause(values[-1] if x in data['minimal_true'] else inv(values[-1]))
 cnf=P/(name+'.cnf')
 with cnf.open('w') as f:
  f.write(f'p cnf {nv} {len(clauses)}\n')
  for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
 remaining=int(seconds-time.monotonic()+start)
 if remaining<=0:break
 print('iteration',iteration,'rows',len(samples),'vars',nv,'clauses',len(clauses),'remaining',remaining,flush=True)
 out=P/(name+f'-{iteration}.out');err=P/(name+f'-{iteration}.err')
 with out.open('w') as fo,err.open('w') as fe:
  cp=subprocess.run([str(SOLVER),'-t',str(remaining),'--seed='+str(seed),str(cnf)],stdout=fo,stderr=fe)
 print('exit',cp.returncode,flush=True)
 if cp.returncode!=10:break
 trues=set()
 for line in out.read_text().splitlines():
  if line.startswith('v '):trues.update(int(t) for t in line[2:].split() if int(t)>0)
 gg=list(g)
 for j,(o,a,b) in controls.items():gg[j]=(int(o in trues),next(k for k,s in enumerate(a) if s in trues),next(k for k,s in enumerate(b) if s in trues))
 def ev(x):
  vs=[bool(x>>i&1) for i in range(N)]
  for o,a,b in gg:vs.append(vs[a] or vs[b] if o else vs[a] and vs[b])
  return vs[-1]
 bad=[x for x in data['minimal_true'] if not ev(x)]+[x for x in data['maximal_false'] if ev(x)]
 print('critical errors',len(bad),flush=True)
 (P/(name+'-candidate.json')).write_text(json.dumps({'gates':gg,'errors':bad}))
 if not bad:print('WITNESS',flush=True);break
 samples=sorted(set(samples)|set(bad[:40]))
