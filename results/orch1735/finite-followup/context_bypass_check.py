import json,sys
from pathlib import Path
witness=Path(sys.argv[1]);d=json.loads(witness.read_text());n=d['n'];gates=d['gates'];output=d.get('output',n+len(gates)-1);edges=d['graph_edges'];positive=[(1<<a)|(1<<b) for a,b in edges];negative=sorted((m for m in range(1<<n) if not any(m>>a&1 and m>>b&1 for a,b in edges)),key=int.bit_count);records=[]
for j,(op,a,b) in enumerate(gates):
 for side,src in enumerate([a,b]):
  masks=positive if op=='or' else negative;certificate=None
  for mask in masks:
   v=[bool(mask>>i&1) for i in range(n)]
   for h,(hop,ha,hb) in enumerate(gates):v.append(v[src] if h==j else (v[ha] and v[hb] if hop=='and' else v[ha] or v[hb]))
   if v[output]!=(op=='or'):certificate=mask;break
  records.append({'gate':j,'op':op,'side':side,'source':src,'essential':certificate is not None,'certificate_mask':certificate,'certificate_kind':'lost positive edge' if op=='or' else 'new independent false positive'})
report={'source':str(witness),'gate_count':len(gates),'all_child_bypasses_essential':all(r['essential'] for r in records),'removable_child_bypasses':[r for r in records if not r['essential']],'records':records,'scope':'necessary condition for leastness only; does not certify a global optimum'}
Path(sys.argv[2]).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='records'},indent=2))
