import importlib.util,json,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('ph',HERE/'pendant_helpers.py');ph=importlib.util.module_from_spec(spec);spec.loader.exec_module(ph);rh=ph.rh
prior=json.loads((HERE/'pendant-audit-results.json').read_text())['cases'];wanted={r['source']:r for r in prior if r.get('max_cover_rise',0)>0 and r['best_profit']==0}
results=[];dirty=[];seen=set();started=time.monotonic()
for c in json.loads((HERE/'saved-amplification-cases.json').read_text()):
 p=wanted.pop(c['source'],None)
 if p is None:continue
 n,e,g,o=c['n'],c['edges'],c['gates'],c['output'];cg,co,_=ph.compact_data(n,g,o)
 ext=ph.extend(n,e,cg,co,p['best_choices']);N=ext['n'];ee=tuple(sorted(tuple(sorted(z)) for z in ext['edges']))
 info,tau,F=rh.graph_data(N,ee);gg,oo,values=ph.compact_data(N,ext['gates'],ext['output'])
 assert values[oo]==F
 profit=len(ee)+tau-1-len(gg);assert profit>=0
 dirt=[j for j,(op,u,v) in enumerate(gg) if op==0 and values[N+j]&~F]
 pairmask=sum(1<<((1<<u)|(1<<v)) for u in range(N) for v in range(u))
 pairdirt=[j for j in dirt if values[N+j]&~F&pairmask]
 record={'source':c['source'],'n':N,'edges':len(ee),'gates':len(gg),'profit':profit,'dirty_and_count':len(dirt),'pair_dirty_and_count':len(pairdirt)};results.append(record)
 if dirt:
  left=[v for v,col in enumerate(info[1]) if col==0];right=[v for v,col in enumerate(info[1]) if col==1]
  dirty.append({**record,'circuit':{'inputs':N,'edges':[(u,v) if info[1][u]==0 else (v,u) for u,v in ee],'gates':gg,'output':oo,'left':left,'right':right}})
summary={'seconds':time.monotonic()-started,'materialized':len(results),'dirty_optimal':len(dirty),'unchecked_wanted':len(wanted)}
(HERE/'materialized-optimal-extensions.json').write_text(json.dumps({'summary':summary,'cases':results,'dirty':dirty},indent=2)+'\n');print(json.dumps(summary),flush=True)
