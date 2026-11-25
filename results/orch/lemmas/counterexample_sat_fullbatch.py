import sys
sys.dont_write_bytecode = True
import argparse,json
from datetime import datetime,timezone
from pathlib import Path
from counterexample_sat_boundary import solve
ap=argparse.ArgumentParser();ap.add_argument('--clean',action='store_true');ap.add_argument('--start',type=int,default=0);ap.add_argument('--stop',type=int,default=25);ap.add_argument('--timeout',type=float,default=90);args=ap.parse_args()
rows=json.loads(Path('/tmp/oec/pequalnp-pilot-51/counterexample_sat_classes.json').read_text())[args.start:args.stop]
for r in rows:
    k=r['clean_upper']-1
    while k>=1:
        print(json.dumps({'starting':r,'gates':k,'clean':args.clean,'at':datetime.now(timezone.utc).isoformat()}),flush=True)
        out=solve(r['N'],r['mask'],k,args.clean,args.timeout)
        out['at']=datetime.now(timezone.utc).isoformat()
        print(json.dumps(out),flush=True)
        if out['status']!='sat':break
        k-=1
