from itertools import combinations, permutations
from pathlib import Path
import subprocess,json,time,argparse
BASE=Path('/tmp/oec/pequalnp-pilot-74')
SOLVER=str(BASE/'toolchain/bin/cadical')
class CNF:
 def __init__(self): self.nv=0;self.cls=[]
 def var(self):self.nv+=1;return self.nv
 def clause(self,*ls):
  if any(x is True for x in ls):return
  self.cls.append([x for x in ls if x is not False])
 def neg(self,v):return not v if type(v)==bool else -v
 def exactly1(self,vs):
  self.clause(*vs)
  # Sequential at-most-one.
  if len(vs)<=1:return
  ps=[self.var() for _ in vs[:-1]]
  self.clause(-vs[0],ps[0])
  for i in range(1,len(vs)-1):
   self.clause(-vs[i],ps[i]);self.clause(-ps[i-1],ps[i]);self.clause(-vs[i],-ps[i-1])
  self.clause(-vs[-1],-ps[-1])
 def emit(self,p):
  with p.open('w') as f:
   f.write(f'p cnf {self.nv} {len(self.cls)}\n')
   for c in self.cls:f.write(' '.join(map(str,c))+' 0\n')
def synth(n,edges,k,label,clean=False,seconds=30,dirty=False,nonstar=False):
 samples=set((1<<a)|(1<<b) for a,b in edges)
 for x in range(1<<n):
  if any(x>>a&1 and x>>b&1 for a,b in edges):continue
  if all(any(((x|(1<<j))>>a&1) and ((x|(1<<j))>>b&1) for a,b in edges) for j in range(n) if not x>>j&1):samples.add(x)
 if clean or dirty:samples.update(x for x in range(1<<n) if x.bit_count()<=2)
 samples=sorted(samples)
 cn=CNF();choices=[];values=[]
 for i in range(k):
  choices.append([(cn.var(),op,a,b) for op in ('and','or') for a,b in combinations(range(n+i),2)])
  cn.exactly1([s for s,*_ in choices[-1]])
  values.append({x:cn.var() for x in samples})
 for i in range(k-1):
  for s,op,a,b in choices[i]:
   key=(op,a,b)
   for t,op2,a2,b2 in choices[i+1]:
    if b2<n+i and (op2,a2,b2)<key:cn.clause(-s,-t)
 def v(w,x):return bool(x>>w&1) if w<n else values[w-n][x]
 for i in range(k):
  for s,op,a,b in choices[i]:
   for x in samples:
    u,w,z=v(a,x),v(b,x),values[i][x]
    if op=='and':
     cn.clause(-s,-z,u);cn.clause(-s,-z,w);cn.clause(-s,z,cn.neg(u),cn.neg(w))
     if clean and x.bit_count()<=2 and not any(x>>a&1 and x>>b&1 for a,b in edges):cn.clause(-s,-z)
    else:
     cn.clause(-s,z,cn.neg(u));cn.clause(-s,z,cn.neg(w));cn.clause(-s,-z,u,w)
 if nonstar:
  af=[cn.var() for _ in range(k)]
  ancestors=[[cn.var() for j in range(i)] for i in range(k)]
  for i in range(k):
   for sel,op,a,b in choices[i]:
    cn.clause(-sel,af[i] if op=='and' else -af[i])
    for j in range(i):
     def prev(w):
      if w<n+j:return False
      if w==n+j:return True
      return ancestors[w-n][j]
     u,vv,z=prev(a),prev(b),ancestors[i][j]
     cn.clause(-sel,z,cn.neg(u));cn.clause(-sel,z,cn.neg(vv));cn.clause(-sel,-z,u,vv)
  witnesses=[]
  for i in range(k):
   for e,f in combinations(edges,2):
    if set(e)&set(f):continue
    w=cn.var();witnesses.append(w)
    x=(1<<e[0])|(1<<e[1]);y=(1<<f[0])|(1<<f[1])
    cn.clause(-w,af[i]);cn.clause(-w,values[i][x]);cn.clause(-w,values[i][y])
    for j in range(i):
     cn.clause(-w,-ancestors[i][j],-af[j],-values[j][x])
     cn.clause(-w,-ancestors[i][j],-af[j],-values[j][y])
  cn.clause(*witnesses)
 if dirty:
  dirty_witness=[]
  for i in range(k):
   andselect=[s for s,op,a,b in choices[i] if op=='and']
   for x in samples:
    if x.bit_count()<=2 and not any(x>>a&1 and x>>b&1 for a,b in edges):
     d=cn.var();dirty_witness.append(d);cn.clause(-d,*andselect);cn.clause(-d,values[i][x])
  cn.clause(*dirty_witness)
 for x in samples:
  want=any(x>>a&1 and x>>b&1 for a,b in edges)
  cn.clause(values[-1][x] if want else -values[-1][x])
 # An optimal circuit can have every nonfinal gate read later.
 for i in range(k-1):cn.clause(*[s for j in range(i+1,k) for s,op,a,b in choices[j] if n+i in [a,b]])
 p=BASE/(label+'.cnf');cn.emit(p)
 out=BASE/(label+'.stdout');err=BASE/(label+'.stderr')
 start=time.monotonic()
 with out.open('w') as f,err.open('w') as e:r=subprocess.run([SOLVER,'-q','-t',str(seconds),str(p)],stdout=f,stderr=e)
 status={10:'SAT',20:'UNSAT'}.get(r.returncode,'UNKNOWN')
 result={'n':n,'edges':edges,'gates':k,'clean':clean,'dirty_required':dirty,'nonstar_required':nonstar,'status':status,'seconds':round(time.monotonic()-start,3),'variables':cn.nv,'clauses':len(cn.cls),'samples':len(samples)}
 if r.returncode==10:
  model={int(x) for line in out.read_text().splitlines() if line.startswith('v ') for x in line.split()[1:] if int(x)>0}
  gs=[(op,a,b) for rows in choices for s,op,a,b in rows if s in model]
  result['circuit']=gs
  assert len(gs)==k
  bad=[];cones=[];tabs=[]
  for i,(op,a,b) in enumerate(gs):
   cone=set()
   for w in [a,b]:
    if w>=n:cone.add(w-n);cone.update(cones[w-n])
   cones.append(cone)
   tab=[]
   for x in range(1<<n):
    u=bool(x>>a&1) if a<n else tabs[a-n][x]
    v_=bool(x>>b&1) if b<n else tabs[b-n][x]
    tab.append(u and v_ if op=='and' else u or v_)
   tabs.append(tab)
   if op=='and':
    owned=[(u,v) for u,v in edges if tab[(1<<u)|(1<<v)] and all(gs[j][0]!='and' or not tabs[j][(1<<u)|(1<<v)] for j in cone)]
    if owned and not any(all(c in e for e in owned) for c in range(n)):bad.append({'gate':i,'owned':owned})
  assert all(tabs[-1][x]==any(x>>a&1 and x>>b&1 for a,b in edges) for x in range(1<<n))
  result['bad_profile']=bad
  result['dirty_and']=[i for i,(op,a,b) in enumerate(gs) if op=='and' and any(tabs[i][x] and x.bit_count()<=2 and not any(x>>u&1 and x>>v&1 for u,v in edges) for x in range(1<<n))]
 return result
if __name__=='__main__':
 pa=argparse.ArgumentParser();pa.add_argument('--n',type=int,default=5);pa.add_argument('--seconds',type=int,default=30);pa.add_argument('--only-cycle',action='store_true');args=pa.parse_args()
 n=args.n
 if args.only_cycle:
  graphs=[[(i,(i+1)%n) for i in range(n)]]
 else:
  pairs=list(combinations(range(n),2));perms=list(permutations(range(n)));canon={}
  for mask in range(1<<len(pairs)):
   es=[e for j,e in enumerate(pairs) if mask>>j&1]
   ns=[set() for _ in range(n)]
   for a,b in es:ns[a].add(b);ns[b].add(a)
   if any(ns[a]&ns[b] for a,b in es):continue
   if any(len(ns[a]&ns[b])>=2 for a,b in pairs):continue
   key=min(tuple(sorted(tuple(sorted((p[a],p[b]))) for a,b in es)) for p in perms)
   canon[key]=es
  graphs=list(canon)
 print('Graph isomorphism classes:',len(graphs),flush=True)
 results=[]
 for j,edges in enumerate(graphs):
  edges=list(edges)
  if not edges:continue
  tau=min(s.bit_count() for s in range(1<<args.n) if all(s>>a&1 or s>>b&1 for a,b in edges))
  bound=len(edges)+tau-1
  if bound<=1:continue
  result=synth(args.n,edges,bound-1,f'star-sat-n{args.n}-{j}-lower',seconds=args.seconds)
  result['cover_bound']=bound
  print(json.dumps(result),flush=True);results.append(result)
  if result['status']=='SAT':
   clean=synth(args.n,edges,bound-1,f'star-sat-n{args.n}-{j}-clean',clean=True,seconds=args.seconds)
   print(json.dumps(clean),flush=True);results.append(clean)
 with (BASE/f'star-sat-n{args.n}-results.json').open('w') as f:json.dump(results,f,indent=2)
