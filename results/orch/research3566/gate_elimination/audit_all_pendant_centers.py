import importlib.util,json,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('ph',HERE/'pendant_helpers.py');ph=importlib.util.module_from_spec(spec);spec.loader.exec_module(ph)
old={r['source']:r for r in json.loads((HERE/'pendant-audit-results.json').read_text())['cases']}
started=time.monotonic();results=[];seen=set();pending=[]
for c in json.loads((HERE/'saved-amplification-cases.json').read_text()):
 n,e,g,o=c['n'],c['edges'],c['gates'],c['output'];key=(n,tuple(sorted(tuple(sorted(x)) for x in e)),tuple(tuple(x) for x in g),o)
 if key in seen:continue
 seen.add(key)
 if time.monotonic()-started>45:pending.append(c['source']);continue
 a=ph.audit_case(n,e,g,o,max_centers=n);previous=old.get(c['source'])
 if previous:assert a['max_cover_rise']>=previous['max_cover_rise']
 results.append({'source':c['source'],'previous_cover_rise':None if previous is None else previous['max_cover_rise'],**a})
 if a.get('witness'):
  (HERE/'all-centers-counterexample.json').write_text(json.dumps({'source':c['source'],**a},indent=2)+'\n');break
summary={'seconds':time.monotonic()-started,'cases':len(results),'pending':len(pending),'max_eligible_centers':max(len(r['eligible']) for r in results),'improved':sum(r['previous_cover_rise'] is not None and r['max_cover_rise']>r['previous_cover_rise'] for r in results),'counterexamples':sum(bool(r.get('witness')) for r in results),'checked_subsets':sum(r['checked_subsets'] for r in results)}
(HERE/'all-pendant-centers-results.json').write_text(json.dumps({'summary':summary,'cases':results,'pending':pending},separators=(',',':'))+'\n');print(json.dumps(summary),flush=True)
