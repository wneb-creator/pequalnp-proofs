import importlib.util,json,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('pendant_helpers',HERE/'pendant_helpers.py');ph=importlib.util.module_from_spec(spec);spec.loader.exec_module(ph);rh=ph.rh
prior=json.loads((HERE/'pendant-audit-results.json').read_text());wanted={r['source']:r for r in prior['cases'] if r.get('max_cover_rise',0)>0}
results=[];started=time.monotonic();controls=[]
for source,n,edges,gates,output in ph.saved_cases():
 if source not in wanted:continue
 r=wanted.pop(source);choices=r['best_choices']
 values,aliases,records,cones=rh.normalize(n,gates,output);output_nodes=[w for w in sorted(records) if (cones[aliases[output]]>>(w-n))&1]
 mapping={i:i for i in range(n)};full=[];full_index={}
 for w in sorted(records):
  op,u,v=records[w];full_index[w]=len(full);full.append((op,mapping[u],mapping[v]));mapping[w]=n+len(full)-1
 translated=[(v,full_index[output_nodes[j]],operand) for v,j,operand in choices]
 ext=ph.extend(n,edges,full,mapping[aliases[output]],translated)
 try:a=rh.audit_case(ext['n'],ext['edges'],ext['gates'],ext['output'])
 except Exception as exc:a={'error':str(exc)}
 out={'source':source,'old_deficit':r['deficit'],'cover_rise':r['max_cover_rise'],'pendant_choices':choices,**a};results.append(out)
 if a.get('witness'):
  (HERE/'combined-counterexample.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True);break
 if not controls and 'error' not in a:
  cg,co,_=ph.compact_data(n,gates,output);control=ph.extend(n,edges,cg,co,choices)
  info,tau,F=rh.graph_data(control['n'],tuple(sorted(tuple(sorted(e)) for e in control['edges'])))
  vv,_,_,_=rh.normalize(control['n'],control['gates'],control['output']);assert vv[control['output']]==F
  control['left']=[i for i,c in enumerate(info[1]) if c==0];control['right']=[i for i,c in enumerate(info[1]) if c==1]
  control['edges']=[(u,v) if info[1][u]==0 else (v,u) for u,v in control['edges']]
  (HERE/'pendant-positive-control.json').write_text(json.dumps({'witness':control,'source':source},indent=2)+'\n');controls.append(source)
summary={'seconds':time.monotonic()-started,'cases':len(results),'valid':sum('error' not in r for r in results),'counterexamples':sum(bool(r.get('witness')) for r in results),'max_combined_profit':max((r.get('best_extension_profit',-100) for r in results),default=None),'errors':[r for r in results if 'error' in r]}
(HERE/'combined-extension-audit-results.json').write_text(json.dumps({'summary':summary,'cases':results},indent=2)+'\n');print(json.dumps({'summary':summary}),flush=True)
