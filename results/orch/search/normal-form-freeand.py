import json,time,z3
from pathlib import Path
from counterexample_freeand import synth
z3.set_param('memory_max_size',256)
cases=[('C6',6,[(i,(i+1)%6) for i in range(6)]),('friendship2',5,[(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)]),('C7',7,[(i,(i+1)%7) for i in range(7)])]
for name,n,edges in cases:
 r=synth(n,edges,len(edges)-2,timeout=120000);r['name']=name
 with Path('/tmp/oec/pequalnp-pilot-55/normal-form-freeand-results.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r),flush=True)
