import ctypes,itertools,json,random,runpy,time
from pathlib import Path
ROOT=Path('/tmp/oec/pequalnp-pilot-87/counterexample');OUT=ROOT/'one-not-local'
core=runpy.run_path(str(ROOT/'synth.py'));target=core['target'];evaluate=core['evaluate']
old=runpy.run_path(str(ROOT/'local_sat.py'));seed=old['seed'];lib=old['lib'];CB=old['CB']
end=0
@CB
def terminate(_):return int(time.monotonic()>end)
def neg(x):return not x if isinstance(x,bool) else -x
class Encode:
 def __init__(self,gs,relax,skip,exact):
  self.n=0;self.cs=[];self.gs=gs;self.relax=relax;self.typ={};self.left={};self.right={};self.rows=[]
  for i in sorted(relax):
   ts=[self.var() for _ in range(3)];a=[self.var() for _ in range(11+i)];b=[self.var() for _ in a]
   self.one(ts);self.one(a);self.one(b);self.clause(-ts[2],b[0])
   for aa in range(len(a)):
    for bb in range(aa):self.clause(ts[2],-a[aa],-b[bb])
   self.typ[i]=ts;self.left[i]=a;self.right[i]=b
  for i,j in itertools.combinations(sorted(relax),2):self.clause(-self.typ[i][2],-self.typ[j][2])
  if exact:self.clause(*(self.typ[i][2] for i in sorted(relax)))
  if len(gs)-1 in relax:self.clause(self.typ[len(gs)-1][1])
  if skip is not None:
   self.clause(self.typ[skip][1])
   for a,b in zip(self.left[skip],self.right[skip]):self.clause(-a,b)
 def var(self):self.n+=1;return self.n
 def clause(self,*xs):
  if any(x is True for x in xs):return
  xs=[x for x in xs if x is not False]
  if any(-x in xs for x in xs):return
  self.cs.append(list(dict.fromkeys(xs)))
 def one(self,xs):
  self.clause(*xs)
  for x,y in itertools.combinations(xs,2):self.clause(-x,-y)
 def binary(self,op,a,b):
  if a==b:return a
  if op==0:
   if a is False or b is False:return False
   if a is True:return b
   if b is True:return a
  else:
   if a is True or b is True:return True
   if a is False:return b
   if b is False:return a
  v=self.var()
  if op==0:self.clause(-v,a);self.clause(-v,b);self.clause(v,neg(a),neg(b))
  else:self.clause(v,neg(a));self.clause(v,neg(b));self.clause(-v,a,b)
  return v
 def row(self,x):
  self.rows.append(x);vs=[False]+[bool(x>>i&1) for i in range(10)]
  for i,(op,a,b) in enumerate(self.gs):
   if i not in self.relax:vs.append(self.binary(op,vs[a],vs[b]));continue
   p=self.var();q=self.var();v=self.var()
   for pin,out in [(self.left[i],p),(self.right[i],q)]:
    for s,val in zip(pin,vs):self.clause(-s,-out,val);self.clause(-s,out,neg(val))
   aa,oo,nn=self.typ[i]
   self.clause(-aa,-v,p);self.clause(-aa,-v,q);self.clause(-aa,v,-p,-q)
   self.clause(-oo,v,-p);self.clause(-oo,v,-q);self.clause(-oo,-v,p,q)
   self.clause(-nn,-v,-p);self.clause(-nn,v,p);vs.append(v)
  self.clause(vs[-1] if target(x) else neg(vs[-1]))
 def load(self,solver,offset=0):
  for c in self.cs[offset:]:
   for v in c:lib.sat_add(solver,v)
   lib.sat_add(solver,0)
 def model(self,solver):
  def chosen(vs):return next(i for i,v in enumerate(vs) if lib.sat_val(solver,v)>0)
  return [(chosen(self.typ[i]),chosen(self.left[i]),chosen(self.right[i])) if i in self.relax else g for i,g in enumerate(self.gs)]
def solver():
 s=lib.sat_init();lib.sat_set_option(s,b'quiet',1);lib.sat_set_terminate(s,None,terminate);return s
def main():
 global end
 start=time.monotonic();rng=random.Random(23738711);gs=seed(rng)
 # SAT positive control: all known gates fixed, at most one NOT.
 c=Encode(gs,set(),None,False)
 for x in range(1024):c.row(x)
 sl=solver();c.load(sl);end=time.monotonic()+10;control=lib.sat_solve(sl);lib.sat_release(sl)
 print(json.dumps({'positive_control':control,'rows':1024,'elapsed':time.monotonic()-start}),flush=True);assert control==10
 counts={0:0,10:0,20:0};trials=[]
 for t in range(100):
  if time.monotonic()-start>=480:break
  if t%8==0:gs=seed(rng)
  d=(t//2)%19
  neighbors={d}
  parents={a-11 for a in gs[d][1:] if a>=11};children={i for i,g in enumerate(gs) if d+11 in g[1:]}
  neighbors|=parents|children
  # Small overlapping topological neighborhoods, never the old unrestricted lane.
  candidates=list(set(range(20))-neighbors);rng.shuffle(candidates)
  size=[3,4,5,6][t%4]
  relax=neighbors|set(candidates[:max(0,size-len(neighbors))])
  if t%4==3:
   for i in list(children):relax.update(j for j,g in enumerate(gs) if i+11 in g[1:])
  c=Encode(gs,relax,d,True)
  rows=[x for x in range(1024) if x.bit_count()<=2 or not target(x)]
  for x in rows:c.row(x)
  sl=solver()
  for vs in list(c.typ.values())+list(c.left.values())+list(c.right.values()):
   for v in vs:lib.sat_freeze(sl,v)
  c.load(sl);trialstart=time.monotonic();rounds=[];outcome=0;witness=None
  meta={'trial':t,'seed':gs,'skip':d,'relax':sorted(relax),'exactly_one_not':True,'time_cap':25,'conflict_cap_per_round':200000}
  for it in range(12):
   remaining=min(start+480,trialstart+25)-time.monotonic()
   if remaining<=0:break
   end=time.monotonic()+remaining;lib.sat_limit(sl,b'conflicts',200000)
   tick=time.monotonic();result=lib.sat_solve(sl)
   detail={'round':it,'result':result,'seconds':time.monotonic()-tick,'rows':len(c.rows),'variables':c.n,'clauses':len(c.cs)}
   if result!=10:rounds.append(detail);outcome=result;break
   candidate=c.model(sl);assert sum(op==2 for op,_,_ in candidate)==1
   misses=[x for x in range(1024) if evaluate(candidate,x)[-1]!=target(x)]
   detail['misses']=len(misses);rounds.append(detail)
   if not misses:
    assert candidate[d][0]==1 and candidate[d][1]==candidate[d][2]
    bypass=candidate[d][1]
    compressed=candidate[:d]+candidate[d+1:]
    def remap(v):return bypass if v==d+11 else v-1 if v>d+11 else v
    compressed=[(op,remap(a),remap(b)) for op,a,b in compressed]
    assert len(compressed)==19 and sum(op==2 for op,_,_ in compressed)==1
    assert all(evaluate(compressed,x)[-1]==target(x) for x in range(1024))
    witness=compressed;outcome=10;break
   fresh=[x for x in misses if x not in c.rows];assert fresh
   # Add all failing rows; model checks always use all1024 rows.
   offset=len(c.cs)
   for x in fresh:c.row(x)
   c.load(sl,offset)
  lib.sat_release(sl);counts[outcome]+=1
  meta.update({'result':outcome,'elapsed':time.monotonic()-trialstart,'rounds':rounds})
  trials.append(meta);(OUT/f'trial-{t:03}.json').write_text(json.dumps(meta,indent=2))
  print(json.dumps({'trial':t,'skip':d,'relax':sorted(relax),'result':outcome,'elapsed':meta['elapsed'],'rounds':rounds,'total_elapsed':time.monotonic()-start}),flush=True)
  if witness:
   a,b=witness[-1][1:];exclusive=[[],[]]
   for x in range(1024):
    vals=evaluate(witness,x)
    if vals[a] and not vals[b]:exclusive[0].append(x)
    if vals[b] and not vals[a]:exclusive[1].append(x)
   (OUT/'witness.json').write_text(json.dumps({'gates':witness,'exclusive':exclusive},indent=2))
   print('EXACT_19_GATE_ONE_NOT_WITNESS',json.dumps(witness),'exclusive',[v[:3] for v in exclusive],flush=True);break
 print(json.dumps({'FINAL':counts,'trials':len(trials),'elapsed':time.monotonic()-start}),flush=True)
 (OUT/'summary.json').write_text(json.dumps({'counts':counts,'trials':len(trials),'elapsed':time.monotonic()-start},indent=2))
if __name__=='__main__':main()
