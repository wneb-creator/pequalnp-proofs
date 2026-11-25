import json,sys
from pathlib import Path
from counterexample_sat import solve
rows=json.loads(Path('/tmp/oec/pequalnp-pilot-51/counterexample_sat_classes.json').read_text())[:5]
clean=bool(int(sys.argv[1]))
for r in rows:
    print(json.dumps({'starting':r,'clean':clean}),flush=True)
    out=solve(r['N'],r['mask'],r['clean_upper']-1,clean,90)
    print(json.dumps(out),flush=True)
