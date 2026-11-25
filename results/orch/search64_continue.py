#!/usr/bin/env python3
import json,time,hashlib
from pathlib import Path
import search64 as m

root=Path('/tmp/oec/pequalnp-pilot-60')
m.JOB=root/'repair-continuation'
m.JOB.mkdir(exist_ok=True)
data=json.loads((root/'tight-circuit.json').read_text())
gates=[tuple(g) for g in data['gates']]
search=m.Search(360,2602)
search.report('continuation_start',skip_completed_repairs=143)
search.consider(gates,data['output'],'initial')
if not search.deletion_sweep(gates,data['output'],'initial'):
 if not search.mutation_sweep(gates,data['output'],'initial'):
  candidates=list(search.near);candidates.sort(key=lambda row:sum(row[2]))
  search.report('continuation_candidates',count=len(candidates))
  completed=0
  for k,(cg,co,errors) in enumerate(candidates):
   if k<143:continue
   before=time.monotonic()
   if search.mutation_sweep(cg,co,f'continuation_repair{k}',exhaustive=True):break
   if time.monotonic()>=search.deadline:break
   completed+=1
  search.report('continuation_finished',completed_remaining_repairs=completed,found=search.found)
print('program_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),flush=True)
