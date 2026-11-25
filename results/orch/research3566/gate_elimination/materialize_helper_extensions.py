import importlib.util,json,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('ph',HERE/'pendant_helpers.py');ph=importlib.util.module_from_spec(spec);spec.loader.exec_module(ph);rh=ph.rh
prior=json.loads((HERE/'pendant-audit-results.json').read_text())['cases'];pendants={r['source']:r for r in prior if r.get('max_cover_rise',0)>0}
results=[];seeds=[];seen=set();started=time.monotonic()
def inspect(ext,source,kind):
 N=ext['n'];ee=tuple(sorted(tuple(sorted(z)) for z in ext['edges']));info,tau,F=rh.graph_data(N,ee)
 g,o,values=ph.compact_data(N,ext['gates'],ext['output']);assert values[o]==F
 profit=len(ee)+tau-1-len(g);assert profit>=0
 dirt=[j for j,(op,u,v) in enumerate(g) if op==0 and values[N+j]&~F]
 record={'source':source,'kind':kind,'n':N,'edges':len(ee),'cover':tau,'gates':len(g),'profit':profit,'dirty_and_count':len(dirt)};results.append(record)
 active=sorted({v for e in ee for v in e});left=[v for v in active if info[1][v]==0];right=[v for v in active if info[1][v]==1]
 if len(left)<=7 and len(right)<=7:
  pm={v:i for i,v in enumerate(left)};pm.update({v:7+i for i,v in enumerate(right)})
  def wire(w):return pm[w] if w<N else 14+w-N
  mapped=[(op,wire(u),wire(v)) for op,u,v in g]
  mappededges=tuple(sorted((pm[u],pm[v]) if info[1][u]==0 else (pm[v],pm[u]) for u,v in ee));key=(mappededges,tuple(mapped))
  if key not in seen:
   seen.add(key);seeds.append({**record,'inputs':14,'edges':mappededges,'gates':mapped,'output':wire(o)})
for c in json.loads((HERE/'saved-amplification-cases.json').read_text()):
 n,e,g,o=c['n'],c['edges'],c['gates'],c['output'];h=rh.audit_case(n,e,g,o)
 if h['deficit']>0 and h['best_extension_profit']==0 and h['best_helpers']:
  inspect(rh.construct_extension(n,e,g,o,h['best_helpers']),c['source'],'helper')
 p=pendants.pop(c['source'],None)
 if p is None:continue
 values,aliases,records,cones=rh.normalize(n,g,o);output_nodes=[w for w in sorted(records) if (cones[aliases[o]]>>(w-n))&1]
 mapping={i:i for i in range(n)};full=[];full_index={}
 for w in sorted(records):
  op,u,v=records[w];full_index[w]=len(full);full.append((op,mapping[u],mapping[v]));mapping[w]=n+len(full)-1
 choices=[(v,full_index[output_nodes[j]],operand) for v,j,operand in p['best_choices']]
 ext=ph.extend(n,e,full,mapping[aliases[o]],choices);combined=rh.audit_case(ext['n'],ext['edges'],ext['gates'],ext['output'])
 if combined['best_extension_profit']==0:
  final=rh.construct_extension(ext['n'],ext['edges'],ext['gates'],ext['output'],combined['best_helpers'])
  inspect(final,c['source'],'combined' if combined['best_helpers'] else 'pendant')
summary={'seconds':time.monotonic()-started,'materialized':len(results),'dirty_optimal':sum(r['dirty_and_count']>0 for r in results),'mapped_seeds':len(seeds),'kinds':{k:sum(r['kind']==k for r in results) for k in ('helper','pendant','combined')}}
(HERE/'materialized-helper-extensions.json').write_text(json.dumps({'summary':summary,'cases':results,'seeds':seeds},separators=(',',':'))+'\n');print(json.dumps(summary),flush=True)
