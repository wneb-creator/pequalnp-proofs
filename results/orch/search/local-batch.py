import subprocess,time
from pathlib import Path
b=Path('/tmp/oec/pequalnp-pilot-31/search')
for distance in [4,5,6,8]:
 name='local'+str(distance);cnf=b/(name+'.cnf');log=b/(name+'.log')
 subprocess.run(['python3',str(b/'synth.py'),'--n','11','--e','16','--t','7','--graph',str(b/'seed11-graph.json'),'--template','/tmp/oec/pequalnp-pilot-31/theory/repair-best.json','--distance',str(distance),'--out',str(cnf)],check=True)
 start=time.time()
 with log.open('w') as f:r=subprocess.run([str(b/'kissat/build/kissat'),'--time=120',str(cnf)],stdout=f,stderr=subprocess.STDOUT)
 print(name,'returncode',r.returncode,'seconds',round(time.time()-start,2),flush=True)
 if r.returncode==10:
  subprocess.run(['python3',str(b/'synth.py'),'--decode',str(cnf.with_suffix('.json')),str(log)],check=True)
  break
