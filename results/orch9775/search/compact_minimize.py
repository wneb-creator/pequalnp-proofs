#!/usr/bin/env python3
"""Deletion-minimize a validated RUP core; retain all trial diagnostics."""
import argparse,gzip,json,pathlib,subprocess,time,random,hashlib
from compact_cnf import SOLVER
from compact_certificate import core
ap=argparse.ArgumentParser();ap.add_argument('stem');ap.add_argument('output');a=ap.parse_args()
d=core(a.stem);stem=pathlib.Path(a.output);stem.parent.mkdir(parents=True,exist_ok=True)
cls=[[v+1 if s else -(v+1) for v,s in c] for c in d['book'][:d['base_count']]]
active=list(range(len(cls)));cnf=stem.with_suffix('.cnf');attempts=0;start=time.time()
def write(ids):cnf.write_text(f'p cnf {len(d["facts"])} {len(ids)}\n'+''.join(' '.join(map(str,cls[i]))+' 0\n' for i in ids))
with gzip.open(stem.with_suffix('.trials.jsonl.gz'),'wt') as log:
 for width in [32,16,8,4,2,1]:
  pos=0
  while pos<len(active):
   removed=active[pos:pos+width];trial=active[:pos]+active[pos+width:]
   if not trial:pos+=width;continue
   write(trial)
   cp=subprocess.run([SOLVER,'-q','--no-witness','-t','1',str(cnf)],capture_output=True,text=True)
   log.write(json.dumps({'attempt':attempts,'removed':removed,'active_count':len(trial),'exit':cp.returncode,'stdout':cp.stdout,'stderr':cp.stderr})+'\n');attempts+=1
   if cp.returncode==20:active=trial
   else:pos+=width
write(active)
metadata={k:d[k] for k in ['I','k','no_exact','facts']};metadata.update(schemes=[d['schemes'][i] for i in active],clauses=[cls[i] for i in active],cnf_sha256=hashlib.sha256(cnf.read_bytes()).hexdigest(),minimized_from=str(a.stem),active_original_ids=active)
stem.with_suffix('.json').write_text(json.dumps(metadata,separators=(',',':'))+'\n')
with stem.with_suffix('.stdout').open('w') as out,stem.with_suffix('.stderr').open('w') as err:
 cp=subprocess.run([SOLVER,'--lrat','--no-binary','-t','10',str(cnf),str(stem.with_suffix('.lrat'))],stdout=out,stderr=err)
assert cp.returncode==20,cp.returncode
dd=core(stem);record={'I':d['I'],'original':len(cls),'minimal':len(active),'dependency_core':dd['base_count'],'learned':len(dd['rows']),'facts':len(dd['facts']),'attempts':attempts,'seconds':time.time()-start}
stem.with_suffix('.minimize.json').write_text(json.dumps(record)+'\n');print(json.dumps(record),flush=True)
