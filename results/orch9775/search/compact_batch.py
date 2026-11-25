#!/usr/bin/env python3
import argparse,json,pathlib,subprocess,time
from compact_cnf import Encoder,SOLVER
ap=argparse.ArgumentParser();ap.add_argument('weights');ap.add_argument('out');ap.add_argument('--seconds',type=int,default=5);a=ap.parse_args()
out=pathlib.Path(a.out);out.mkdir(parents=True,exist_ok=True)
masks=json.loads(pathlib.Path(a.weights).read_text())['survivors']['11']
results=[]
for m in masks:
 k=m.bit_count()-3
 stem=out/f'case-{m}'
 en=Encoder(m,k).build();cnf=en.save(stem)
 start=time.time()
 with stem.with_suffix('.stdout').open('w') as f,stem.with_suffix('.stderr').open('w') as g:
  cp=subprocess.run([SOLVER,'--lrat','--no-binary','-t',str(a.seconds),str(cnf),str(stem.with_suffix('.lrat'))],stdout=f,stderr=g)
 r={'I':m,'k':k,'vars':len(en.facts),'clauses':len(en.clauses),'exit_code':cp.returncode,'seconds':time.time()-start,'verdict':{10:'SAT',20:'UNSAT',0:'UNKNOWN'}.get(cp.returncode,'ERROR')}
 results.append(r);stem.with_suffix('.result.json').write_text(json.dumps(r)+'\n')
 (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
 print(json.dumps(r),flush=True)
