#!/usr/bin/env python3
import argparse,json,pathlib,subprocess,sys,hashlib,time
from compact_cnf import SOLVER
from compact_certificate import core,emit
ap=argparse.ArgumentParser();ap.add_argument('stem');ap.add_argument('output');ap.add_argument('--seconds',type=int,default=5);a=ap.parse_args()
src=pathlib.Path(a.stem);out=pathlib.Path(a.output);out.mkdir(parents=True,exist_ok=True)
options=[[],['--plain'],['--plain','--no-minimize'],['--plain','--shrink=0'],['--plain','--seed=1'],['--plain','--seed=2'],['--unsat'],['--no-vivify','--no-elim']]
results=[]
for i,opts in enumerate(options):
 stem=out/f'variant-{i}';stem.with_suffix('.json').write_bytes(src.with_suffix('.json').read_bytes())
 start=time.time()
 with stem.with_suffix('.stdout').open('w') as stdout,stem.with_suffix('.stderr').open('w') as stderr:
  cp=subprocess.run([SOLVER,'--lrat','--no-binary','-t',str(a.seconds),*opts,str(src.with_suffix('.cnf')),str(stem.with_suffix('.lrat'))],stdout=stdout,stderr=stderr)
 r={'variant':i,'options':opts,'exit_code':cp.returncode,'seconds':time.time()-start}
 if cp.returncode==20:
  d=core(stem);name=('W' if d['no_exact'] else 'P')+str(d['I']);text=emit(d,name,True)
  stem.with_suffix('.lean').write_text(text);r.update(base=d['base_count'],rows=len(d['rows']),facts=len(d['facts']),bytes=len(text))
 results.append(r);(out/'results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(r),flush=True)
