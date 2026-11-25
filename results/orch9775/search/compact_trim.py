#!/usr/bin/env python3
import argparse,json,pathlib,hashlib,subprocess,time
from compact_cnf import SOLVER
from compact_certificate import core
ap=argparse.ArgumentParser();ap.add_argument('stem');ap.add_argument('output');ap.add_argument('--seconds',type=int,default=5);a=ap.parse_args()
data=core(a.stem);stem=pathlib.Path(a.output);stem.parent.mkdir(parents=True,exist_ok=True)
clauses=[[v+1 if s else -(v+1) for v,s in c] for c in data['book'][:data['base_count']]]
cnf=stem.with_suffix('.cnf');cnf.write_text(f'p cnf {len(data["facts"])} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
metadata={k:data[k] for k in ['I','k','no_exact','facts','schemes']};metadata.update(clauses=clauses,cnf_sha256=hashlib.sha256(cnf.read_bytes()).hexdigest(),trimmed_from=str(a.stem))
stem.with_suffix('.json').write_text(json.dumps(metadata,separators=(',',':'))+'\n')
with stem.with_suffix('.stdout').open('w') as out,stem.with_suffix('.stderr').open('w') as err:
 r=subprocess.run([SOLVER,'--lrat','--no-binary','-t',str(a.seconds),str(cnf),str(stem.with_suffix('.lrat'))],stdout=out,stderr=err)
assert r.returncode==20,r.returncode
dd=core(stem);print(json.dumps({'input':len(clauses),'output':dd['base_count'],'learned':len(dd['rows']),'facts':len(dd['facts'])}))
