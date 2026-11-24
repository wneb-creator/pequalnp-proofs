import subprocess,time,json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-31/search')
cases=[(4,3,2),(5,5,3),(5,6,3),(6,6,4),(6,7,3),(6,7,4),(7,9,4),(7,8,4)]
for n,e,t in cases:
 name=f'n{n}-e{e}-t{t}';cnf=base/(name+'.cnf');log=base/(name+'.log')
 subprocess.run(['python3',str(base/'synth.py'),'--n',str(n),'--e',str(e),'--t',str(t),'--out',str(cnf)],check=True)
 start=time.time()
 with log.open('w') as f:r=subprocess.run([str(base/'kissat/build/kissat'),'--time=120',str(cnf)],stdout=f,stderr=subprocess.STDOUT)
 print(name,'returncode',r.returncode,'seconds',round(time.time()-start,2),flush=True)
 if r.returncode==10:
  with (base/(name+'-witness.json')).open('w') as f:subprocess.run(['python3',str(base/'synth.py'),'--decode',str(cnf.with_suffix('.json')),str(log)],stdout=f,stderr=subprocess.STDOUT,check=True)
  print('FOUND',name,flush=True)
