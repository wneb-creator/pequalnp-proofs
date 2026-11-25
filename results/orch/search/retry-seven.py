import json,runpy
from pathlib import Path
b=Path('/tmp/oec/pequalnp-pilot-74')
s=runpy.run_path('/workspace/pequalnp-proofs/results/orch/search/star-sat.py')
rs=json.loads(Path('/workspace/pequalnp-proofs/results/orch/search/star-seven-results.json').read_text())
out=[]
for i,r in enumerate(rs):
 if r['status']!='UNKNOWN':continue
 label='star-seven-retry-'+str(i)
 q=s['synth'](r['n'],r['edges'],r['gates'],label,seconds=120)
 q['previous_seconds']=r['seconds'];q['cover_bound']=r['cover_bound']
 out.append(q);print(json.dumps(q),flush=True)
 (b/'star-seven-retry-results.json').write_text(json.dumps(out,indent=2))
 (b/(label+'.cnf')).unlink()
 if (b/'pause-sat').exists():break
