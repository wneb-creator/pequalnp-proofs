import argparse,importlib.util,json,math,random,time
from functools import lru_cache
from pathlib import Path

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('reusable_helpers',HERE/'reusable_helpers.py')
rh=importlib.util.module_from_spec(spec);spec.loader.exec_module(rh)
N=14;L=7;R=7;INPUT=rh.inputs(N)
PAIR=[(u,v,(1<<u)|(1<<v),INPUT[u]&INPUT[v]) for u in range(L) for v in range(L,N)]
BAD=[(1<<u)|(1<<v) for u in range(N) for v in range(u+1,N) if (u<L)==(v<L)]
SING=[1<<u for u in range(N)]
COUNTS={'evaluated':0,'valid':0,'safe_helper_cases':0,'full_audits':0,'incomplete_audits':0}

@lru_cache(maxsize=32768)
def graph_info(key):
 rows=[0]*L;truth=0;edges=[]
 for i,(u,v,pair,mask) in enumerate(PAIR):
  if (key>>i)&1:rows[u]|=1<<(v-L);truth|=mask;edges.append((u,v))
 c4=sum((rows[i]&rows[j]).bit_count()*((rows[i]&rows[j]).bit_count()-1)//2 for i in range(L) for j in range(i))
 mate=[-1]*R
 def aug(u,seen):
  candidates=rows[u]
  while candidates:
   bit=candidates&-candidates;candidates^=bit;v=bit.bit_length()-1
   if seen[v]:continue
   seen[v]=True
   if mate[v]<0 or aug(mate[v],seen):mate[v]=u;return True
  return False
 tau=sum(aug(u,[False]*R) for u in range(L))
 return truth,len(edges),tau,c4,tuple(edges)

@lru_cache(maxsize=32768)
def geometry(key):
 adj=[0]*N
 for u,v in graph_info(key)[4]:adj[u]|=1<<v;adj[v]|=1<<u
 components=[];unseen=(1<<N)-1
 while unseen:
  comp=0;todo=unseen&-unseen
  while todo:
   bit=todo&-todo;todo^=bit;u=bit.bit_length()-1
   if comp&bit:continue
   comp|=bit;todo|=adj[u]&~comp
  components.append(comp);unseen&=~comp
 return tuple(adj),tuple(components)

@lru_cache(maxsize=65536)
def geometrically_safe(key,S):
 adj,components=geometry(key);left=(1<<L)-1;right=((1<<N)-1)^left
 if any((S&v).bit_count()>1 for v in adj):return False
 return all(not(S&comp&left and S&comp&right) for comp in components)

@lru_cache(maxsize=16384)
def or_support(S):
 value=0
 while S:
  bit=S&-S;S^=bit;value|=INPUT[bit.bit_length()-1]
 return value

def cheap_helpers(key,F,values,records,cones,output_cone):
 helpers=[]
 for w in records:
  value=values[w];S=sum(((value>>(1<<i))&1)<<i for i in range(N))
  if S.bit_count()<2 or not geometrically_safe(key,S):continue
  ors=or_support(S)
  if value&~(ors|F):continue
  assert not(ors&~value)
  helpers.append((w,S,cones[w],S.bit_count()-1))
 # Each helper must pay for gates used by no other helper or the output.
 # Ignoring all remaining shared costs gives an optimistic, cheap upper bound.
 improvement_bound=0
 for i,(_,S,cone,weight) in enumerate(helpers):
  others=output_cone
  for j,h in enumerate(helpers):
   if i!=j:others|=h[2]
  improvement_bound+=max(0,weight-(cone&~others).bit_count())
 return helpers,improvement_bound

def evaluate(g,min_edges=14,force_audit=False):
 COUNTS['evaluated']+=1
 values,aliases,records,cones=rh.normalize(N,g,N+len(g)-1)
 out=values[-1];output_cone=cones[aliases[-1]];cost=output_cone.bit_count()
 bad=sum((out>>p)&1 for p in BAD)+2*sum((out>>p)&1 for p in SING)
 key=sum(((out>>p)&1)<<i for i,(_,_,p,_) in enumerate(PAIR))
 F,m,tau,c4,edges=graph_info(key);extra=(out&~F).bit_count();assert not(F&~out)
 gain=m+tau-1-cost;amplification=gain;audit=None;helpers=[];upper=gain
 valid=extra==bad==c4==0 and m>0
 if valid:
  COUNTS['valid']+=1
  helpers,improvement=cheap_helpers(key,F,values,records,cones,output_cone);upper+=improvement
  if helpers:COUNTS['safe_helper_cases']+=1
  if improvement>0 or gain>0 or force_audit:
   COUNTS['full_audits']+=1
   audit=rh.audit_case(N,edges,g,N+len(g)-1,subset_budget_s=0.05,build_extension=True)
   amplification=audit['best_extension_profit']
   if not audit['subset_complete'] and not audit.get('witness'):COUNTS['incomplete_audits']+=1
   assert amplification<=upper
 signature=tuple(sorted((h[1],(h[2]&~output_cone).bit_count()) for h in helpers))
 metrics={'base_gain':gain,'amplification_profit':amplification,'optimistic_profit':upper,
  'extra_rows':extra,'bad_pairs':bad,'four_cycles':c4,'edges':m,'cover':tau,'cost':cost,
  'safe_helpers':len(helpers),'helper_signatures':signature,'valid':valid,'graph_key':key}
 score=8*amplification+0.2*m-(12*bad+24*c4+2*math.log2(1+extra))
 if m<min_edges:score=-1000000
 return score,metrics,audit

def shuffled(g,rng):
 remaining=set(range(len(g)));mapping={i:i for i in range(N)};out=[]
 while remaining:
  available=[i for i in remaining if all(w in mapping for w in g[i][1:]) and (i!=len(g)-1 or len(remaining)==1)]
  i=rng.choice(available);remaining.remove(i);op,u,v=g[i]
  out.append((op,mapping[u],mapping[v]));mapping[N+i]=N+len(out)-1
 return tuple(out)

def relabeled(g,rng):
 p=rng.sample(range(L),L)+rng.sample(range(L,N),R)
 return tuple((op,p[u] if u<N else u,p[v] if v<N else v) for op,u,v in g)

def load_seeds():
 names=['evolution-178.json','evolution-v2-3566.json','evolution-fano-10760.json','evolution-dirty-3566179.json']
 seeds=[];seen=set()
 for name in names:
  data=json.loads((HERE/name).read_text())
  for kind in ('best_valid','best_dirty'):
   r=data.get(kind)
   if not r:continue
   g=tuple(tuple(x) for x in r['gates'])
   if g not in seen:seen.add(g);seeds.append(g)
 rows=json.loads((HERE/'helper-dp-audit-results.json').read_text())['cases']
 useful=[r for r in rows if any(h['incremental_cost']==0 for h in r['helpers'])]
 useful.sort(key=lambda r:(r['best_extension_profit'],r['best_extension_profit']+r['deficit']),reverse=True)
 csrc=HERE.parent/'certificate_search';helper_seeds=json.loads((csrc/'c8-helper-seeds.json').read_text())
 for r in useful[:8]:
  path=Path(r['source']);case=json.loads(path.read_text());idx=r['helper_index']
  if path.parent.name not in ('c8-helpers-2-3-all','c8-helpers-2-3-all-part2'):continue
  raw=[['or',0,1]]+helper_seeds[idx]['gates']+case['gates'];assert case['output']==8+len(raw)-1
  pm=[0,1,2,3,7,8,9,10]
  def wire(w):return pm[w] if w<8 else w-8+N
  g=tuple((0 if op in (0,'and') else 1,wire(u),wire(v)) for op,u,v in raw)
  if g not in seen:seen.add(g);seeds.append(g)
 return seeds

def mutate(g,rng):
 h=list(g)
 for _ in range(rng.choices((1,2,3,4),(70,21,7,2))[0]):
  i=rng.randrange(len(h));op,u,v=h[i];kind=rng.randrange(10)
  if kind==0:op^=1
  elif kind<5:u=rng.randrange(N+i)
  elif kind<9:v=rng.randrange(N+i)
  else:op=rng.randrange(2);u=rng.randrange(N+i);v=rng.randrange(N+i)
  h[i]=(op,u,v)
 return tuple(h)

def rank(m):return (m['amplification_profit'],m['amplification_profit']-m['base_gain'],m['edges'])
def snapshot(g,m,audit):
 return {'inputs':N,'gates':g,'output':N+len(g)-1,'edges':graph_info(m['graph_key'])[4],
  'metrics':m,'audit':audit}
def log_metrics(m):return {k:v for k,v in m.items() if k not in ('graph_key','helper_signatures')}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=180);ap.add_argument('--seed',type=int,default=178)
 ap.add_argument('--min-edges',type=int,default=14);ap.add_argument('--output',required=True);ap.add_argument('--validate-only',action='store_true');args=ap.parse_args()
 rng=random.Random(args.seed);seeds=load_seeds()
 if args.validate_only:
  checks=[]
  for i,g in enumerate(seeds):
   _,m,_=evaluate(g,args.min_edges)
   direct=rh.audit_case(N,graph_info(m['graph_key'])[4],g,N+len(g)-1)
   assert direct['subset_complete'] and direct['best_extension_profit']==m['amplification_profit']
   checks.append({'seed':i,**log_metrics(m)})
  Path(args.output).write_text(json.dumps({'checks':checks,'counters':COUNTS},indent=2)+'\n')
  print(json.dumps({'validated_seeds':len(checks),'counters':COUNTS}),flush=True);return
 start=time.monotonic();deadline=start+args.seconds;next_report=0;restarts=0
 archive={};keys=set();best=None;best_graph=None;witness=None
 while time.monotonic()<deadline:
  if archive and rng.random()<0.6:g=rng.choice(list(archive.values()))[0]
  else:g=rng.choice(seeds)
  g=shuffled(relabeled(g,rng),rng);score,m,audit=evaluate(g,args.min_edges)
  end=min(deadline,time.monotonic()+rng.uniform(1,5));restarts+=1;temp=rng.choice((0.3,0.7,1.3,2.5))
  while time.monotonic()<end:
   h=mutate(g,rng);hs,hm,ha=evaluate(h,args.min_edges)
   if hm['valid']:
    keys.add(hm['graph_key'])
    if best is None or rank(hm)>rank(best[1]):
     best=(h,hm,ha);print(json.dumps({'event':'best_amplification','seconds':time.monotonic()-start,**log_metrics(hm)}),flush=True)
    if best_graph is None or (hm['base_gain'],hm['edges'])>(best_graph[1]['base_gain'],best_graph[1]['edges']):best_graph=(h,hm,ha)
    archivekey=(hm['graph_key'],hm['helper_signatures'])
    if hm['amplification_profit']>=-1 and hm['edges']>=args.min_edges:
     archive[archivekey]=(h,hm,ha)
     if len(archive)>192:del archive[rng.choice(list(archive))]
    if hm['amplification_profit']>0:
     assert ha and ha.get('witness');witness={'source':snapshot(h,hm,ha),'extension':ha['witness']}
     print(json.dumps({'event':'VERIFIED_EXTENSION','witness':witness}),flush=True);break
   if hs>=score or rng.random()<math.exp(max(-700,(hs-score)/temp)):g,score,m,audit=h,hs,hm,ha
   if time.monotonic()-start>=next_report:
    print(json.dumps({'event':'progress','seconds':time.monotonic()-start,'restarts':restarts,'valid_graphs':len(keys),'counters':COUNTS,'current':log_metrics(m)}),flush=True);next_report+=10
  if witness:break
 result={'seconds':time.monotonic()-start,'restarts':restarts,'valid_graphs':len(keys),'counters':COUNTS,
  'witness':witness,'best_amplification':None if best is None else snapshot(*best),'best_graph':None if best_graph is None else snapshot(*best_graph)}
 Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'event':'finished','seconds':result['seconds'],'valid_graphs':len(keys),'counters':COUNTS,'counterexample':witness is not None}),flush=True)

if __name__=='__main__':main()
