import z3,json
from pathlib import Path
from counterexample_sparse_sat import synth
from counterexample_canonical import pair_reps
z3.set_param('memory_max_size',256)
for name,n,e,start,finish in [('C5',5,[(0,1),(1,2),(2,3),(3,4),(4,0)],7,11),('theta233',7,[(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)],11,14)]:
 reps,_=pair_reps(n,e)
 for size in range(start,finish):
  r=synth(n,e,size,timeout=180000,maxorder=True,firstpairs=reps,localcuts=True,maxor=len(e)-2);r.update(name=name,maxor=len(e)-2)
  with Path('/tmp/oec/pequalnp-pilot-55/counterexample-or-count-results.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(json.dumps(r),flush=True)
  if r['result']=='sat':break
