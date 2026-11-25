#!/usr/bin/env python3
import argparse,gzip,hashlib,json,pathlib,random,shutil,subprocess,time
from compact_cnf import SOLVER
from compact_certificate import core,emit
ap=argparse.ArgumentParser();ap.add_argument('stem');ap.add_argument('output');ap.add_argument('--seeds',type=int,default=50);a=ap.parse_args()
src=pathlib.Path(a.stem);out=pathlib.Path(a.output);out.mkdir(parents=True,exist_ok=True);orig=json.loads(src.with_suffix('.json').read_text());best=10**9;start=time.time()
with gzip.open(out/'all-diagnostics.jsonl.gz','wt') as log:
 for seed in range(a.seeds):
  rng=random.Random(seed);order=list(range(len(orig['clauses'])));rng.shuffle(order)
  d=dict(orig);d['clauses']=[orig['clauses'][i][:] for i in order];d['schemes']=[orig['schemes'][i] for i in order]
  for c in d['clauses']:rng.shuffle(c)
  stem=out/'current';cnf=stem.with_suffix('.cnf');cnf.write_text(f'p cnf {len(d["facts"])} {len(d["clauses"])}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in d['clauses']))
  d['cnf_sha256']=hashlib.sha256(cnf.read_bytes()).hexdigest();d['shuffle_seed']=seed;d['shuffled_from']=str(src);stem.with_suffix('.json').write_text(json.dumps(d,separators=(',',':'))+'\n')
  cp=subprocess.run([SOLVER,'--lrat','--no-binary','--shuffle','--shufflerandom',f'--seed={seed}','-t','2',str(cnf),str(stem.with_suffix('.lrat'))],capture_output=True,text=True)
  r={'seed':seed,'exit_code':cp.returncode,'stdout':cp.stdout,'stderr':cp.stderr,'source_sha256':d['cnf_sha256']}
  if cp.returncode==20:
   dd=core(stem);name=('W' if dd['no_exact'] else 'P')+str(dd['I']);s=emit(dd,name,True);r.update(bytes=len(s),base=dd['base_count'],rows=len(dd['rows']))
   if len(s)<best:
    best=len(s)
    for suffix in ['.cnf','.json','.lrat']:shutil.copyfile(stem.with_suffix(suffix),(out/'best').with_suffix(suffix))
    (out/'best.lean').write_text(s);(out/'best.result.json').write_text(json.dumps({k:v for k,v in r.items() if k not in ['stdout','stderr']})+'\n');print(json.dumps({'seed':seed,'bytes':len(s),'base':dd['base_count'],'rows':len(dd['rows']),'seconds':time.time()-start}),flush=True)
  log.write(json.dumps(r)+'\n')
print(json.dumps({'finished':a.seeds,'best_bytes':best,'seconds':time.time()-start}),flush=True)
