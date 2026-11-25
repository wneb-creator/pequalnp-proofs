import importlib.util,json,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('ph',HERE/'pendant_helpers.py');ph=importlib.util.module_from_spec(spec);spec.loader.exec_module(ph);rh=ph.rh
started=time.monotonic();results=[];seen=set()
for c in json.loads((HERE/'saved-amplification-cases.json').read_text()):
 n,e,g,o=c['n'],c['edges'],c['gates'],c['output'];key=(n,tuple(sorted(tuple(sorted(x)) for x in e)),tuple(tuple(x) for x in g),o)
 if key in seen:continue
 seen.add(key)
 h=rh.audit_case(n,e,g,o);p=ph.audit_case(n,e,g,o);combined=None
 if p['max_cover_rise']:
  values,aliases,records,cones=rh.normalize(n,g,o);output_nodes=[w for w in sorted(records) if (cones[aliases[o]]>>(w-n))&1]
  mapping={i:i for i in range(n)};full=[];full_index={}
  for w in sorted(records):
   op,u,v=records[w];full_index[w]=len(full);full.append((op,mapping[u],mapping[v]));mapping[w]=n+len(full)-1
  translated=[(v,full_index[output_nodes[j]],operand) for v,j,operand in p['best_choices']]
  ext=ph.extend(n,e,full,mapping[aliases[o]],translated)
  combined=rh.audit_case(ext['n'],ext['edges'],ext['gates'],ext['output'])
 results.append({'source':c['source'],'helper':h,'pendant':p,'combined':combined})
summary={'seconds':time.monotonic()-started,'cases':len(results),'positive_helpers':sum(bool(r['helper'].get('witness')) for r in results),'positive_pendant':sum(bool(r['pendant'].get('witness')) for r in results),'positive_combined':sum(bool((r['combined'] or {}).get('witness')) for r in results)}
(HERE/'replayed-saved-audits.json').write_text(json.dumps({'summary':summary,'cases':results},separators=(',',':'))+'\n');print(json.dumps(summary),flush=True)
