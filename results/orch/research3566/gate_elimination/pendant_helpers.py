import importlib.util,json,time
from functools import lru_cache
from itertools import combinations
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('rh',HERE/'reusable_helpers.py');rh=importlib.util.module_from_spec(spec);spec.loader.exec_module(rh)

def compact_data(n,gates,output):
 values,aliases,records,cones=rh.normalize(n,gates,output);cone=cones[aliases[output]]
 mapping={i:i for i in range(n)};compact=[];truths=list(rh.inputs(n))
 for w in sorted(records):
  if not(cone>>(w-n))&1:continue
  op,u,v=records[w];compact.append((op,mapping[u],mapping[v]));truths.append(values[w]);mapping[w]=n+len(compact)-1
 return compact,mapping[aliases[output]],truths

@lru_cache(maxsize=65536)
def augmented_cover(n,edges,centers):
 extended=edges+tuple((v,n+i) for i,v in enumerate(centers));info=rh.color_graph(n+len(centers),extended)
 assert info is not None
 adj,colors,_=info;mate={}
 def aug(u,seen):
  for v in adj[u]:
   if v in seen:continue
   seen.add(v)
   if v not in mate or aug(mate[v],seen):mate[v]=u;return True
  return False
 return sum(aug(u,set()) for u in range(len(adj)) if colors[u]==0)

def assignment(centers,eligibility):
 centers=sorted(centers,key=lambda v:len(eligibility[v]));chosen=[];used=set()
 def solve(i):
  if i==len(centers):return True
  v=centers[i]
  for gate,operand in eligibility[v]:
   if gate in used:continue
   used.add(gate);chosen.append((v,gate,operand))
   if solve(i+1):return True
   chosen.pop();used.remove(gate)
  return False
 return list(chosen) if solve(0) else None

def extend(n,edges,gates,output,choices):
 N=n+len(choices);selected={gate:(i,operand) for i,(_,gate,operand) in enumerate(choices)}
 mapping={i:i for i in range(n)};new=[]
 for j,(op,u,v) in enumerate(gates):
  a,b=mapping[u],mapping[v]
  if j in selected:
   i,operand=selected[j];assert op==0
   other=b if operand==0 else a
   new.append((1,other,n+i));other_new=N+len(new)-1
   if operand==0:b=other_new
   else:a=other_new
  new.append((op,a,b));mapping[n+j]=N+len(new)-1
 return {'n':N,'inputs':N,'edges':list(edges)+[(v,n+i) for i,(v,_,_) in enumerate(choices)],'gates':new,'output':mapping[output]}

def audit_case(n,edges,gates,output=None,max_centers=4,generalized=True):
 edges=tuple(sorted({tuple(sorted(e)) for e in edges}));gates=tuple(tuple(g) for g in gates)
 if output is None:output=n+len(gates)-1
 _,tau,F=rh.graph_data(n,edges);cg,co,values=compact_data(n,gates,output)
 if values[co]!=F:raise ValueError('original circuit fails full truth function')
 eligible={};literal=0;general=0;todo=[co];seen=set()
 while todo:
  w=todo.pop()
  if w<n or w in seen:continue
  seen.add(w);j=w-n;op,u,v=cg[j]
  if op==1:todo.extend((u,v));continue
  for operand,f in enumerate((u,v)):
   if f<n:center=f;literal+=1
   elif generalized:
    support=[i for i in range(n) if (values[f]>>(1<<i))&1]
    if len(support)!=1:continue
    center=support[0]
    if values[f]&~(rh.inputs(n)[center]|F):continue
    assert not(rh.inputs(n)[center]&~values[f]);general+=1
   else:continue
   eligible.setdefault(center,[]).append((j,operand))
 deficit=len(cg)-(len(edges)+tau-1);best_rise=0;best_choices=[];checked=0
 for k in range(1,min(max_centers,len(eligible))+1):
  for centers in combinations(sorted(eligible),k):
   choices=assignment(centers,eligible)
   if choices is None:continue
   checked+=1;rise=augmented_cover(n,edges,tuple(sorted(centers)))-tau
   if rise>best_rise:best_rise=rise;best_choices=choices
   if rise>deficit:break
  if best_rise>deficit:break
 result={'n':n,'edges':len(edges),'cover':tau,'raw_gates':len(gates),'normalized_gates':len(cg),'deficit':deficit,
  'literal_choices':literal,'generalized_choices':general,'eligible':eligible,'checked_subsets':checked,
  'max_cover_rise':best_rise,'best_choices':best_choices,'best_profit':best_rise-deficit}
 if best_rise>deficit:
  ext=extend(n,edges,cg,co,best_choices);N=ext['n'];ee=tuple(sorted(tuple(sorted(e)) for e in ext['edges']))
  info,newtau,newF=rh.graph_data(N,ee);newvals,_,_,_=rh.normalize(N,ext['gates'],ext['output'])
  assert newvals[ext['output']]==newF
  assert newtau-tau==best_rise
  assert len(ee)+newtau-1-len(ext['gates'])==best_rise-deficit
  ext['edges']=[(u,v) if info[1][u]==0 else (v,u) for u,v in ext['edges']]
  ext['left']=[i for i,c in enumerate(info[1]) if c==0];ext['right']=[i for i,c in enumerate(info[1]) if c==1]
  result['witness']={**ext,'cover':newtau,'profit':best_rise-deficit,'verified_assignments':1<<N}
 return result

def saved_cases():
 base=HERE.parent;src=base/'certificate_search'
 paths=[Path(p) for p in (HERE/'helper-audit-files.txt').read_text().splitlines()]
 for p in paths:
  if p.suffix!='.json':continue
  if not ((p.parent.name=='gate_elimination' and p.name.startswith('evolution')) or
          (p.parent.name=='finite_search' and p.name.endswith('.witness.json')) or
          (p.parent.name=='certificate_search' and p.name in ('c6-baseline-sat.json','bip5x6-mixed-greedy.json'))):continue
  for name,n,e,g,o in rh.records_from_file(p):yield str(p)+':'+name,n,e,g,o
 graph=json.loads((src/'c8-helper-dp-rows.json').read_text())['graph'];seeds=json.loads((src/'c8-helper-seeds.json').read_text())
 known=set((HERE/'helper-dp-case-files.txt').read_text().splitlines())|set((HERE/'helper-all-safe-files.txt').read_text().splitlines())
 groups=[('c8-one-helper','c8-one-helper-results.json'),('c8-helpers-2-3-all','c8-helpers-2-3-all-results.json'),('c8-helpers-2-3-all-part2','c8-helpers-2-3-all-part2-results.json'),('c8-all-safe-one-helper','c8-all-safe-one-helper-results.json')]
 for directory,aggregate in groups:
  for e in json.loads((src/aggregate).read_text())['results']:
   p=src/directory/f"case-{e['index']}.json";assert str(p) in known;c=json.loads(p.read_text())
   if directory=='c8-one-helper':prefix=[['or',0,1],e['helper']]
   elif directory=='c8-all-safe-one-helper':prefix=[['or',0,1],['or',2,3],['or',4,7],['or',5,6],e['helper']]
   else:prefix=[['or',0,1]]+seeds[e['index']]['gates']
   yield str(p),8,graph['edges'],prefix+c['gates'],c['output']

if __name__=='__main__':
 started=time.monotonic();seen=set();results=[]
 for source,n,e,g,o in saved_cases():
  key=(n,tuple(sorted(tuple(sorted(x)) for x in e)),tuple(tuple(x) for x in g),o)
  if key in seen:continue
  seen.add(key)
  try:r=audit_case(n,e,g,o)
  except Exception as exc:r={'error':str(exc)}
  r={'source':source,**r};results.append(r)
  if r.get('max_cover_rise',0)>0 or r.get('error'):print(json.dumps(r),flush=True)
  if r.get('witness'):
   (HERE/'pendant-counterexample.json').write_text(json.dumps(r,indent=2)+'\n');break
 summary={'seconds':time.monotonic()-started,'cases':len(results),'valid':sum('error' not in r for r in results),
  'with_generalized_operands':sum(r.get('generalized_choices',0)>0 for r in results),'with_cover_rise':sum(r.get('max_cover_rise',0)>0 for r in results),
  'counterexamples':sum(bool(r.get('witness')) for r in results),'errors':[r for r in results if 'error' in r]}
 (HERE/'pendant-audit-results.json').write_text(json.dumps({'summary':summary,'cases':results},indent=2)+'\n');print(json.dumps({'summary':summary}),flush=True)
