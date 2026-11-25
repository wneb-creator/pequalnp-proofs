import argparse,json,time
from functools import lru_cache
from itertools import combinations
from pathlib import Path

@lru_cache(maxsize=16)
def inputs(n):
 result=[];total=1<<n
 for p in range(n):
  period=2<<p;v=((1<<(1<<p))-1)<<(1<<p)
  while period<total:v|=v<<period;period*=2
  result.append(v)
 return tuple(result)

def color_graph(n,edges):
 adj=[set() for _ in range(n)]
 for u,v in edges:
  if u==v:return None
  adj[u].add(v);adj[v].add(u)
 colors=[None]*n;components=[None]*n;component=0
 for start in range(n):
  if colors[start] is not None:continue
  colors[start]=0;components[start]=component;todo=[start]
  while todo:
   u=todo.pop()
   for v in adj[u]:
    if colors[v] is None:colors[v]=colors[u]^1;components[v]=component;todo.append(v)
    elif colors[v]==colors[u]:return None
  component+=1
 return adj,colors,components

@lru_cache(maxsize=256)
def graph_data(n,edges):
 info=color_graph(n,edges)
 if info is None:raise ValueError('graph not bipartite')
 adj,colors,components=info
 assert all(len(adj[u]&adj[v])<=1 for u in range(n) for v in range(u))
 mate={}
 def aug(u,seen):
  for v in adj[u]:
   if v in seen:continue
   seen.add(v)
   if v not in mate or aug(mate[v],seen):mate[v]=u;return True
  return False
 tau=sum(aug(u,set()) for u in range(n) if colors[u]==0)
 ins=inputs(n);F=0
 for u,v in edges:F|=ins[u]&ins[v]
 return info,tau,F

def normalize(n,gates,output):
 ins=inputs(n);values=list(ins);aliases=list(range(n));byvalue={v:i for i,v in enumerate(ins)}
 cheap={}
 for u in range(n):
  for v in range(u):
   cheap[ins[u]&ins[v]]=(0,u,v);cheap[ins[u]|ins[v]]=(1,u,v)
 records={};cones={i:0 for i in range(n)}
 for j,(op,u,v) in enumerate(gates):
  if op in ('and','AND'):op=0
  elif op in ('or','OR'):op=1
  if op not in (0,1) or not(0<=u<n+j and 0<=v<n+j):raise ValueError('invalid gate')
  value=values[u]&values[v] if op==0 else values[u]|values[v];values.append(value)
  if value in byvalue:aliases.append(byvalue[value]);continue
  w=n+j;aliases.append(w);byvalue[value]=w
  records[w]=cheap.get(value,(op,aliases[u],aliases[v]));_,a,b=records[w]
  cones[w]=(1<<j)|cones[a]|cones[b]
 if not 0<=output<len(values):raise ValueError('output out of bounds')
 return values,aliases,records,cones

def extended_edges(n,edges,helpers):
 result=list(edges)
 for i,h in enumerate(helpers):
  center=n+2*i;leaf=center+1
  result.extend((center,s) for s in h['support']);result.append((center,leaf))
 return result

def construct_extension(n,edges,gates,output,chosen):
 values,aliases,records,cones=normalize(n,gates,output)
 union=cones[aliases[output]]
 for h in chosen:union|=cones[h['wire']]
 N=n+2*len(chosen);mapping={i:i for i in range(n)};newgates=[]
 for w in sorted(records):
  if not(union>>(w-n))&1:continue
  op,u,v=records[w];newgates.append((op,mapping[u],mapping[v]));mapping[w]=N+len(newgates)-1
 out=mapping[aliases[output]]
 for i,h in enumerate(chosen):
  center=n+2*i;leaf=center+1
  newgates.append((1,mapping[h['wire']],leaf));a=N+len(newgates)-1
  newgates.append((0,center,a));b=N+len(newgates)-1
  newgates.append((1,out,b));out=N+len(newgates)-1
 return {'n':N,'edges':extended_edges(n,edges,chosen),'gates':newgates,'output':out}

def audit_case(n,edges,gates,output=None,subset_budget_s=0.5,build_extension=True):
 edges=tuple(sorted({tuple(sorted(e)) for e in edges}));gates=tuple(tuple(g) for g in gates)
 if output is None:output=n+len(gates)-1
 (adj,colors,components),tau,F=graph_data(n,edges)
 values,aliases,records,cones=normalize(n,gates,output)
 if values[output]!=F:raise ValueError('full truth table disagrees with graph')
 potential=len(edges)+tau-1;output_cone=cones[aliases[output]]
 rejected={'small_support':0,'color_conflict':0,'common_neighbor':0,'extra_true_rows':0}
 helpers=[]
 for w in sorted(records):
  value=values[w];S=[i for i in range(n) if (value>>(1<<i))&1]
  if len(S)<2:rejected['small_support']+=1;continue
  bycomponent={};conflict=False
  for i in S:
   if components[i] in bycomponent and bycomponent[components[i]]!=colors[i]:conflict=True
   bycomponent[components[i]]=colors[i]
  if conflict:rejected['color_conflict']+=1;continue
  if any(len(set(S)&adj[i])>1 for i in range(n)):
   rejected['common_neighbor']+=1;continue
  ors=0
  for i in S:ors|=inputs(n)[i]
  assert not(ors&~value)
  if value&~(ors|F):rejected['extra_true_rows']+=1;continue
  helpers.append({'wire':w,'support':S,'cone':cones[w],'incremental_cost':(cones[w]&~output_cone).bit_count(),
                  'single_profit':potential+len(S)-1-(cones[w]|output_cone).bit_count()})
 helpers.sort(key=lambda h:(h['single_profit'],len(h['support'])),reverse=True)
 best_profit=potential-output_cone.bit_count();best=[];states=0;timed_out=False
 deadline=time.monotonic()+subset_budget_s
 suffix=[0]*(len(helpers)+1)
 for i in range(len(helpers)-1,-1,-1):suffix[i]=suffix[i+1]+len(helpers[i]['support'])-1
 def search(i,chosen,union,weight):
  nonlocal best_profit,best,states,timed_out
  states+=1
  if states%128==0 and time.monotonic()>deadline:timed_out=True;return
  profit=potential+weight-union.bit_count()
  if profit>best_profit:best_profit=profit;best=list(chosen)
  if best_profit>0:return
  if i==len(helpers) or potential+weight+suffix[i]-union.bit_count()<=best_profit:return
  h=helpers[i]
  if all(len(set(h['support'])&set(q['support']))<=1 for q in chosen):
   choice=chosen+[h]
   if color_graph(n+2*len(choice),extended_edges(n,edges,choice)) is not None:
    search(i+1,choice,union|h['cone'],weight+len(h['support'])-1)
  if not timed_out and best_profit<=0:search(i+1,chosen,union,weight)
 search(0,[],output_cone,0)
 result={'n':n,'edges':len(edges),'cover':tau,'raw_gates':len(gates),'normalized_output_gates':output_cone.bit_count(),
   'deficit':output_cone.bit_count()-potential,'helpers':helpers,'rejected':rejected,
   'best_extension_profit':best_profit,'best_helpers':best,'subset_states':states,'subset_complete':not timed_out and best_profit<=0}
 if best_profit>0 and build_extension:
  ext=construct_extension(n,edges,gates,output,best)
  ne=ext['n'];ee=tuple(sorted(tuple(sorted(e)) for e in ext['edges']))
  _,etau,ef=graph_data(ne,ee);vals,_,_,_=normalize(ne,ext['gates'],ext['output'])
  assert vals[ext['output']]==ef
  assert etau==tau+len(best)
  assert len(ee)+etau-1-len(ext['gates'])==best_profit
  result['witness']={**ext,'cover':etau,'profit':best_profit,'verified_assignments':1<<ne}
 return result

def records_from_file(path):
 s=json.loads(path.read_text());own='gate_elimination' in path.parts
 if not isinstance(s,dict):return []
 context=s.get('graph',{})
 if not isinstance(context,dict):context={}
 records=[]
 def collect(record,name):
  if not isinstance(record,dict) or not isinstance(record.get('gates'),list):return
  edges=record.get('edges',context.get('edges',s.get('edges')))
  if edges is None:return
  n=record.get('n',record.get('inputs',context.get('n',s.get('n',14 if own else None))))
  if n is None:return
  g=record['gates'];o=record.get('output',n+len(g)-1)
  # Evolution outputs refer to normalized gates; the raw genome always outputs its last gate.
  if 'normalized_gates' in record:o=n+len(g)-1
  records.append((name+'/raw',n,edges,g,o))
  if 'normalized_gates' in record:
   ng=record['normalized_gates'];records.append((name+'/normalized',n,edges,ng,record.get('output',n+len(ng)-1)))
 collect(s,'top')
 for key in ('best_valid','best_dirty','witness','best'):collect(s.get(key),key)
 return records

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--manifest',required=True);ap.add_argument('--output',required=True);args=ap.parse_args()
 paths=[Path(p) for p in Path(args.manifest).read_text().splitlines()]
 chosen=[]
 for p in paths:
  if p.suffix!='.json':continue
  if p.parent.name=='gate_elimination' and p.name.startswith('evolution'):chosen.append(p)
  elif p.parent.name=='finite_search' and p.name.endswith('.witness.json'):chosen.append(p)
  elif p.parent.name=='certificate_search' and p.name in ('c6-baseline-sat.json','bip5x6-mixed-greedy.json'):chosen.append(p)
 seen=set();results=[]
 for path in chosen:
  for name,n,edges,gates,out in records_from_file(path):
   key=(n,tuple(sorted(tuple(sorted(e)) for e in edges)),tuple(tuple(g) for g in gates),out)
   if key in seen:continue
   seen.add(key)
   try:r=audit_case(n,edges,gates,out)
   except Exception as exc:r={'error':str(exc)}
   r={'source':str(path),'record':name,**r};results.append(r)
   if r.get('helpers') or r.get('error'):print(json.dumps(r),flush=True)
   if r.get('witness'):break
  if results and results[-1].get('witness'):break
 summary={'circuits':len(results),'valid':sum('error' not in r for r in results),
  'with_safe_helpers':sum(bool(r.get('helpers')) for r in results),
  'counterexamples':sum(bool(r.get('witness')) for r in results),
  'errors':[r for r in results if 'error' in r]}
 Path(args.output).write_text(json.dumps({'summary':summary,'cases':results},indent=2)+'\n')
 print(json.dumps({'summary':summary}),flush=True)
