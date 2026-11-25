import argparse,json,random,subprocess,time
from pathlib import Path

class CNF:
 def __init__(self): self.n=1; self.cs=[[1]]
 def var(self): self.n+=1; return self.n
 def clause(self,*lits):
  s=set(lits)
  if 1 in s or any(-x in s for x in s): return
  s.discard(-1); self.cs.append(list(s))
 def atleast_one(self,xs): self.clause(*xs)
 def gate(self,a,b,op):
  if a==b:return a
  if a==-b:return -1 if op==0 else 1
  if op==0:
   if -1 in (a,b):return -1
   if a==1:return b
   if b==1:return a
  else:
   if 1 in (a,b):return 1
   if a==-1:return b
   if b==-1:return a
  o=self.var()
  if op==0:self.clause(-o,a);self.clause(-o,b);self.clause(o,-a,-b)
  else:self.clause(o,-a);self.clause(o,-b);self.clause(-o,a,b)
  return o
 def select(self,ss,vs):
  if len(set(vs))==1:return vs[0]
  o=self.var()
  for s,v in zip(ss,vs):self.clause(-s,-o,v);self.clause(-s,o,-v)
  return o
 def typed(self,a,b,t):
  o=self.var()
  self.clause(t,-o,a);self.clause(t,-o,b);self.clause(t,o,-a,-b)
  self.clause(-t,o,-a);self.clause(-t,o,-b);self.clause(-t,-o,a,b)
  return o
 def dump(self,p,flips=set()):
  with p.open('w') as f:
   f.write(f'p cnf {self.n} {len(self.cs)}\n')
   for c in self.cs:f.write(' '.join(str(-x if abs(x) in flips else x) for x in c)+' 0\n')

def cases(adj,r):
 l=len(adj); pos=[(1<<i)|(1<<(l+j)) for i,a in enumerate(adj) for j in range(r) if a>>j&1]
 neg=[]
 for s in range(1<<l):
  cover=0
  for i,a in enumerate(adj):
   if s>>i&1:cover|=a
  t=((1<<r)-1)^cover; closure=sum(1<<i for i,a in enumerate(adj) if not(a&t))
  if closure==s:neg.append(s|(t<<l))
 return [(x,True) for x in pos]+[(x,False) for x in neg]

def evaluate(n,gs,x):
 w=[bool(x>>i&1) for i in range(n)]
 for op,a,b in gs:w.append((w[a] or w[b]) if op else (w[a] and w[b]))
 return w[-1]

def build(n,gs,free,tests,positive_support=False,dirty=None):
 c=CNF();params={}
 for i in free:
  m=n+i; sa=[c.var() for _ in range(m)];sb=[c.var() for _ in range(m)];t=c.var()
  c.atleast_one(sa);c.atleast_one(sb)
  for j,a in enumerate(sa):c.clause(-a,*sb[j:])
  params[i]=(sa,sb,t)
 if len(params)==len(gs):
  for i in range(len(gs)-1):
   sa,sb,t=params[i];na,nb,nt=params[i+1];dep=nb[n+i]
   c.clause(dep,-t,nt)
   for hi in range(len(sa)):
    for lo in range(hi):
     c.clause(dep,-sa[hi],-na[lo],t,nt)
     c.clause(dep,-sa[hi],-na[lo],-t,-nt)
 for wire in range(n+len(gs)-1):
  if any(j not in params and wire in g[1:] for j,g in enumerate(gs)):continue
  uses=[sel[wire] for j,(sa,sb,t) in params.items() if wire<n+j for sel in [sa,sb]]
  c.clause(*uses)
 supports=[[] for _ in gs]
 for x,wanted in tests:
  ws=[1 if x>>i&1 else -1 for i in range(n)]
  for i,g in enumerate(gs):
   if i in params:
    sa,sb,t=params[i];a=c.select(sa,ws);b=c.select(sb,ws);out=c.typed(a,b,t)
   else:
    op,a,b=g;out=c.gate(ws[a],ws[b],op)
   ws.append(out)
   if wanted:supports[i].append(out)
  c.clause(ws[-1] if wanted else -ws[-1])
 if positive_support:
  for supp in supports:c.clause(*supp)
 if dirty is not None:
  ws=[1 if dirty>>i&1 else -1 for i in range(n)];hits=[]
  for i,g in enumerate(gs):
   if i in params:
    sa,sb,t=params[i];aa=c.select(sa,ws);bb=c.select(sb,ws);out=c.typed(aa,bb,t);hits.append(c.gate(out,-t,0))
   else:
    op,u,v=g;out=c.gate(ws[u],ws[v],op)
    if op==0:hits.append(out)
   ws.append(out)
  c.clause(-ws[-1]);c.clause(*hits)
 return c,params

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--case',choices=['arc','private','full','control'],default='arc');ap.add_argument('--seconds',type=int,default=60);ap.add_argument('--output',required=True);ap.add_argument('--free',type=int,default=0);ap.add_argument('--seed',type=int,default=132);ap.add_argument('--gates',type=int);ap.add_argument('--iterations',type=int,default=30);ap.add_argument('--pin',action='store_true');ap.add_argument('--full-positive',action='store_true');ap.add_argument('--dirty',type=int);a=ap.parse_args()
 rng=random.Random(a.seed);d=Path(a.output);d.mkdir(parents=True,exist_ok=True)
 if a.case=='arc':n=10;gs=[[0,0,1] for _ in range(a.gates or 14)];tests=cases([7,25,42,52],6)
 elif a.case=='private':n=14;gs=[[0,0,1] for _ in range(a.gates or 18)];tests=cases([71,153,298,564],10)
 else:
  n=26;gs=json.loads(Path('/tmp/oec/pequalnp-pilot-132/circuit-search/'+('seed64.json' if a.case=='control' else 'best.json')).read_text());data=json.loads(Path('/tmp/oec/pequalnp-pilot-132/circuit-search/cases.json').read_text());tests=[(x,True) for x in data['positive']]+[(x,False) for x in data['negative']]
 if a.free:
  bad=[x for x,y in tests if evaluate(n,gs,x)!=y]
  if not bad:bad=[tests[0][0]]
  values=[[bool(x>>i&1) for i in range(n)] for x in bad]
  for op,u,v in gs:
   for w in values:w.append((w[u] or w[v]) if op else(w[u] and w[v]))
  candidates=[i for i in range(len(gs)) if gs[i][0]==0]
  rng.shuffle(candidates)
  defect=[i for i in candidates if any(u<n and any(x>>u&1 for x in bad) for u in gs[i][1:])]
  selected=set(defect[:1] or candidates[:1])
  stack=list(selected)
  while stack and len(selected)<a.free:
   i=stack.pop()
   for u in gs[i][1:]:
    if u>=n and u-n not in selected:
     selected.add(u-n);stack.append(u-n)
     if len(selected)>=a.free:break
  for i in candidates:
   if len(selected)>=max(1,a.free//3):break
   selected.add(i)
  while len(selected)<a.free:
   i=rng.choice(tuple(selected));op,u,v=gs[i]
   near=[u-n,v-n]+[j for j,g in enumerate(gs) if i+n in g[1:]]
   near=[j for j in near if j>=0 and j not in selected]
   selected.add(rng.choice(near) if near and rng.random()<0.8 else rng.randrange(len(gs)))
  free=sorted(selected)
 else:free=list(range(len(gs)))
 chosen=rng.sample([t for t in tests if t[1]],3)+rng.sample([t for t in tests if not t[1]],3)
 if a.case=='full':chosen.extend(t for t in tests if evaluate(n,gs,t[0])!=t[1])
 if a.full_positive:chosen=list(dict.fromkeys([t for t in tests if t[1]]+chosen))
 meta={'case':a.case,'n':n,'gates':len(gs),'free':free,'tests':len(tests),'seed':a.seed,'dirty':a.dirty,'full_positive':a.full_positive};(d/'meta.json').write_text(json.dumps(meta,indent=2));print(meta,flush=True)
 start=time.time()
 for k in range(a.iterations):
  c,params=build(n,gs,free,chosen,a.full_positive,a.dirty)
  if a.pin:
   for i,(sa,sb,t) in params.items():
    op,u,v=gs[i];u,v=sorted((u,v));c.clause(sa[u]);c.clause(sb[v]);c.clause(t if op else -t)
  flips=set()
  if a.case in ['full','control']:
   for i,(sa,sb,t) in params.items():
    op,u,v=gs[i];u,v=sorted((u,v));flips.update(x for j,x in enumerate(sa) if j!=u);flips.update(x for j,x in enumerate(sb) if j!=v)
    if op==0:flips.add(t)
  p=d/f'problem-{k}.cnf';c.dump(p,flips);print('round',k,'cases',len(chosen),'variables',c.n,'clauses',len(c.cs),flush=True)
  log=d/f'solver-{k}.log'
  with log.open('w') as f:r=subprocess.run(['nice','-n','10','/tmp/oec/pequalnp-pilot-132/sat-resynthesis/kissat-4.0.4-linux-amd64',f'--time={a.seconds}',str(p)],stdout=f,stderr=subprocess.STDOUT)
  text=log.read_text();(d/f'tests-{k}.json').write_text(json.dumps(chosen));p.unlink();print('solver_exit',r.returncode,'elapsed',round(time.time()-start,2),flush=True)
  if r.returncode!=10:return
  model={int(x) for line in text.splitlines() if line.startswith('v ') for x in line[2:].split() if int(x)>0}
  model=model^flips
  out=[g.copy() for g in gs]
  for i,(sa,sb,t) in params.items():out[i]=[int(t in model),next(j for j,v in enumerate(sa) if v in model),next(j for j,v in enumerate(sb) if v in model)]
  wrong=[(x,y) for x,y in tests if evaluate(n,out,x)!=y];(d/f'candidate-{k}.json').write_text(json.dumps(out));print('wrong',len(wrong),flush=True)
  if not wrong:
   (d/'solution.json').write_text(json.dumps(out));print('SOLVED',flush=True);return
  rng.shuffle(wrong);chosen.extend(wrong[:min(32,len(wrong))])

if __name__=='__main__':main()
