import importlib.util,json,time
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-178/gap3566');own=base/'gate_elimination';src=base/'certificate_search'
spec=importlib.util.spec_from_file_location('reusable_helpers',own/'reusable_helpers.py');lib=importlib.util.module_from_spec(spec);spec.loader.exec_module(lib)
graph=json.loads((src/'c8-helper-dp-rows.json').read_text())['graph'];n=graph['n'];edges=graph['edges']
seeds=json.loads((src/'c8-helper-seeds.json').read_text())
known=set((own/'helper-dp-case-files.txt').read_text().splitlines());allresults=[];started=time.monotonic();seen=set()
for directory,aggregate in [('c8-one-helper','c8-one-helper-results.json'),('c8-helpers-2-3-all','c8-helpers-2-3-all-results.json'),('c8-helpers-2-3-all-part2','c8-helpers-2-3-all-part2-results.json')]:
 entries=json.loads((src/aggregate).read_text())['results']
 for entry in entries:
  p=src/directory/f"case-{entry['index']}.json"
  if str(p) not in known:raise ValueError('case not discovered: '+str(p))
  case=json.loads(p.read_text())
  prefix=[['or',0,1]]+([entry['helper']] if directory=='c8-one-helper' else seeds[entry['index']]['gates'])
  gates=prefix+case['gates'];out=case['output'];key=(tuple(tuple(g) for g in gates),out)
  if key in seen:continue
  seen.add(key)
  try:r=lib.audit_case(n,edges,gates,out)
  except Exception as exc:r={'error':str(exc)}
  r={'source':str(p),'helper_index':entry['index'],**r};allresults.append(r)
  if r.get('best_extension_profit',-100)>0 or 'error' in r:print(json.dumps(r),flush=True)
  if r.get('witness'):
   (own/'helper-dp-counterexample.json').write_text(json.dumps({'witness':r['witness'],'source':str(p),'source_gates':gates,'source_output':out},indent=2)+'\n');break
 if allresults and allresults[-1].get('witness'):break
summary={'seconds':time.monotonic()-started,'cases':len(allresults),'valid':sum('error' not in r for r in allresults),'counterexamples':sum(bool(r.get('witness')) for r in allresults),'with_safe_helpers':sum(bool(r.get('helpers')) for r in allresults),'with_multiple_safe_helpers':sum(len(r.get('helpers',[]))>=2 for r in allresults),'max_profit':max((r.get('best_extension_profit',-100) for r in allresults),default=None),'errors':[r for r in allresults if 'error' in r]}
(own/'helper-dp-audit-results.json').write_text(json.dumps({'summary':summary,'cases':allresults},indent=2)+'\n');print(json.dumps({'summary':summary}),flush=True)
