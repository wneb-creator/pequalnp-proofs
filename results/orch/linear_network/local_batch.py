import subprocess,json,time
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-85/linear_network/local-sat')
base.mkdir(exist_ok=True)
solver='/tmp/oec/pequalnp-pilot-85/sat-tool/cadical-rel-3.1.0/build/cadical'
script='/tmp/oec/pequalnp-pilot-85/counterexample/synthesize.py'
fixed='/tmp/oec/pequalnp-pilot-85/counterexample/best.json'
groups=[
 [13,14,15,16,17,23],
 [0,1,13,15,16,17],
 [10,12,13,15,16,17],
 [13,15,16,17,22,23],
 [0,13,14,15,16,17],
 [1,12,15,17,22,23],
 [18,19,20,21,22,23],
 [0,1,13,14,15,16,17,22,23],
 [10,11,12,13,14,15,16,17,21,22,23],
]
for i,g in enumerate(groups):
 out=base/f'case-{i:02d}'
 log=base/f'case-{i:02d}.log'
 print('START',i,'unlock',g,flush=True)
 cmd=['python3',script,'--solver',solver,'--out',str(out),'--fixed',fixed,'--unlock',','.join(map(str,g)),'--seconds','60','--rounds','12']
 with log.open('w') as f:p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
 text=log.read_text()
 print('FINISH',i,'exit',p.returncode, 'last',text.splitlines()[-1] if text else '',flush=True)
 if (out/'FOUND.json').exists():
  print('FOUND',out,flush=True);break
