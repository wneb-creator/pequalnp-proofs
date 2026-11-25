#!/usr/bin/env python3
import argparse,concurrent.futures,hashlib,json,pathlib,subprocess,time
ap=argparse.ArgumentParser();ap.add_argument('--folder',default='/workspace/pequalnp-proofs/results/orch9775/search/compact-packed');ap.add_argument('--all',action='store_true');a=ap.parse_args()
base=pathlib.Path(a.folder);logs=base/'checks';logs.mkdir(exist_ok=True)
rows=json.loads((base/'summary.json').read_text());jobs=[r for r in rows if a.all or r['name'] not in ['P177','W127','W16256','W8488','P63']]
def run(row):
 src=base/(row['name']+'.lean');start=time.time();stem=logs/row['name']
 with stem.with_suffix('.stdout').open('w') as out,stem.with_suffix('.stderr').open('w') as err:
  cp=subprocess.run(['lean','-R',str(base),'-o',str(src.with_suffix('.olean')),str(src)],stdout=out,stderr=err)
 result={**row,'exit_code':cp.returncode,'seconds':time.time()-start,'sha256':hashlib.sha256(src.read_bytes()).hexdigest()}
 stem.with_suffix('.result.json').write_text(json.dumps(result)+'\n');print(json.dumps(result),flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(run,jobs))
