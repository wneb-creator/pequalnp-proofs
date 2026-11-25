import importlib.util,json
from pathlib import Path
OUT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('ao_search',OUT/'ao_search.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
rows=json.loads((OUT/'classes33.json').read_text());results=[]
for k,row in enumerate(rows):
 if row['cost']==1:
  P,L,E=row['P'],row['L'],row['E'];n=P+L
  f=[any((x>>p)&(x>>(P+l))&1 for p,l in E) for x in range(1<<n)]
  assert all([bool(x>>i&1) for x in range(1<<n)]!=f for i in range(n)) and any(f)
  rc=20;print('zero-gate case excluded by direct truth-table comparison',flush=True)
 else:rc=m.solve(row['P'],row['L'],row['E'],row['cost']-1,f'census33-{k:02d}',60)
 results.append({**row,'returncode':rc})
 (OUT/'census33-results.json').write_text(json.dumps(results,indent=2))
print('CENSUS',len(results),'UNSAT',sum(r['returncode']==20 for r in results),flush=True)
