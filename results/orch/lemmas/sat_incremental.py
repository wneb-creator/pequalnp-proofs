import argparse,ctypes,json,random,time
from pathlib import Path
from sat_resynthesis import CNF,evaluate,cases

class Incremental:
 def __init__(self):
  lib=ctypes.CDLL('/tmp/oec/pequalnp-pilot-132/sat-resynthesis/cadical/build/libcadical.so');self.lib=lib
  lib.ipasir_init.restype=ctypes.c_void_p
  for name,args,ret in [('ipasir_add',[ctypes.c_void_p,ctypes.c_int],None),('ipasir_val',[ctypes.c_void_p,ctypes.c_int],ctypes.c_int),('ipasir_solve',[ctypes.c_void_p],ctypes.c_int),('ipasir_release',[ctypes.c_void_p],None)]:
   f=getattr(lib,name);f.argtypes=args;f.restype=ret
  self.callback_type=ctypes.CFUNCTYPE(ctypes.c_int,ctypes.c_void_p);lib.ipasir_set_terminate.argtypes=[ctypes.c_void_p,ctypes.c_void_p,self.callback_type]
  self.s=lib.ipasir_init()
 def add(self,clauses,flips):
  for cs in clauses:
   for x in cs:self.lib.ipasir_add(self.s,-x if abs(x) in flips else x)
   self.lib.ipasir_add(self.s,0)
 def solve(self,secs):
  end=time.monotonic()+secs;self.cb=self.callback_type(lambda _:int(time.monotonic()>=end));self.lib.ipasir_set_terminate(self.s,None,self.cb)
  return self.lib.ipasir_solve(self.s)
 def model(self,n,flips):return {v for v in range(1,n+1) if (self.lib.ipasir_val(self.s,v)>0) != (v in flips)}
 def close(self):self.lib.ipasir_release(self.s)

def add_case(c,n,gs,params,x,wanted,dirty=False):
 ws=[1 if x>>i&1 else -1 for i in range(n)];hits=[]
 for i,g in enumerate(gs):
  if i in params:
   sa,sb,t=params[i];aa=c.select(sa,ws);bb=c.select(sb,ws);out=c.typed(aa,bb,t)
   if dirty:hits.append(c.gate(out,-t,0))
  else:
   op,u,v=g;out=c.gate(ws[u],ws[v],op)
   if dirty and op==0:hits.append(out)
  ws.append(out)
 c.clause(ws[-1] if wanted else -ws[-1])
 if dirty:c.clause(*hits)
 return ws[n:]

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--meta',required=True);ap.add_argument('--seconds',type=int,default=60);ap.add_argument('--rounds',type=int,default=30);ap.add_argument('--output',required=True);ap.add_argument('--full-positive',action='store_true');ap.add_argument('--all-cases',action='store_true');ap.add_argument('--normal',action='store_true');a=ap.parse_args()
 meta=json.loads(Path(a.meta).read_text());n=meta['n'];free=meta['free'];kind=meta['case'];rng=random.Random(meta['seed']);d=Path(a.output);d.mkdir(parents=True,exist_ok=True)
 if kind in ['full','control']:
  gs=json.loads(Path('/tmp/oec/pequalnp-pilot-132/circuit-search/'+('seed64.json' if kind=='control' else 'best.json')).read_text());data=json.loads(Path('/tmp/oec/pequalnp-pilot-132/circuit-search/cases.json').read_text());tests=[(x,True) for x in data['positive']]+[(x,False) for x in data['negative']]
 else:
  adj,r=(meta['adj'],meta['r']) if kind=='custom' else (([7,25,42,52],6) if kind=='arc' else ([71,153,298,564],10));tests=cases(adj,r);gs=[];outs=[]
  omit=sum(x.bit_count() for x in adj)+len(adj)-1>meta['gates']
  for i,mask in enumerate(adj):
   neighbors=[len(adj)+j for j in range(r) if mask>>j&1]
   if i==0 and omit:neighbors.pop()
   wire=neighbors[0]
   for v in neighbors[1:]:gs.append([1,wire,v]);wire=n+len(gs)-1
   gs.append([0,i,wire]);outs.append(n+len(gs)-1)
  wire=outs[0]
  for v in outs[1:]:gs.append([1,wire,v]);wire=n+len(gs)-1
  assert len(gs)==meta['gates']
 (d/'seed.json').write_text(json.dumps(gs));(d/'meta.json').write_text(json.dumps(meta,indent=2));c=CNF();params={};flips=set()
 for i in free:
  m=n+i;sa=[c.var() for _ in range(m)];sb=[c.var() for _ in range(m)];t=c.var();c.atleast_one(sa);c.atleast_one(sb)
  for j,sel in enumerate(sa):c.clause(-sel,*sb[j:])
  params[i]=sa,sb,t
  if True:
   op,u,v=gs[i];u,v=sorted((u,v));flips.update(x for j,x in enumerate(sa) if j!=u);flips.update(x for j,x in enumerate(sb) if j!=v)
   if not op:flips.add(t)
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
 solver=Incremental();added=set();chosen=rng.sample([t for t in tests if t[1]],3)+rng.sample([t for t in tests if not t[1]],3)
 if kind=='full':chosen.extend(t for t in tests if evaluate(n,gs,t[0])!=t[1])
 if a.full_positive:chosen=[t for t in tests if t[1]]+chosen
 if a.all_cases:chosen=list(tests)
 if a.normal:chosen=[t for t in tests if t[1]]+chosen+[(1<<v,False) for v in range(n)]
 dirty=meta.get('dirty')
 if dirty is not None:add_case(c,n,gs,params,dirty,False,True)
 clause_count=0;rowvalues={};start=time.monotonic()
 for k in range(a.rounds):
  for x,y in chosen:
   if (x,y) not in added:rowvalues[x]=add_case(c,n,gs,params,x,y);added.add((x,y))
  if a.normal and k==0:
   positives=[x for x,y in tests if y]
   for j in range(len(gs)):
    pv=[rowvalues[x][j] for x in positives];c.clause(*pv)
    for v in range(n):c.clause(-rowvalues[1<<v][j],*[rowvalues[x][j] for x in positives if not(x>>v&1)])
    if j in params:
     sa,sb,t=params[j]
     for ei,x in enumerate(positives):
      u,v=[v for v in range(n) if x>>v&1];base=[-pv[ei]]+pv[:ei]+pv[ei+1:]
      c.clause(*base,sa[u]);c.clause(*base,sb[v]);c.clause(*base,-t)
  solver.add(c.cs,flips);clause_count+=len(c.cs);c.cs=[]
  print('round',k,'cases',len(added),'variables',c.n,'clauses',clause_count,flush=True);result=solver.solve(a.seconds);print('result',result,'elapsed',round(time.monotonic()-start,2),flush=True)
  (d/f'tests-{k}.json').write_text(json.dumps(sorted(added)))
  if result!=10:break
  model=solver.model(c.n,flips);out=[g.copy() for g in gs]
  for i,(sa,sb,t) in params.items():out[i]=[int(t in model),next(j for j,v in enumerate(sa) if v in model),next(j for j,v in enumerate(sb) if v in model)]
  wrong=[t for t in tests if evaluate(n,out,t[0])!=t[1]];(d/f'candidate-{k}.json').write_text(json.dumps(out));print('wrong',len(wrong),'positive',sum(y for _,y in wrong),flush=True)
  if not wrong:(d/'solution.json').write_text(json.dumps(out));print('SOLVED',flush=True);break
  rng.shuffle(wrong);chosen=wrong[:min(32,len(wrong))]
 solver.close()

if __name__=='__main__':main()
