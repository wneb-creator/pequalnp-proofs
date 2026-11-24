import json,subprocess,time
from pathlib import Path
b=Path('/tmp/oec/pequalnp-pilot-31/search')
for i in range(1,5):
 name='n6-class'+str(i);gp=b/(name+'-graph.json');d=json.loads(gp.read_text());cnf=b/(name+'.cnf');log=b/(name+'.log')
 subprocess.run(['python3',str(b/'synth.py'),'--n','6','--e','7','--t',str(d['tau']),'--graph',str(gp),'--out',str(cnf)],check=True)
 st=time.time()
 with log.open('w')as f:r=subprocess.run([str(b/'kissat/build/kissat'),'--time=120',str(cnf)],stdout=f,stderr=subprocess.STDOUT)
 print(name,'returncode',r.returncode,'seconds',round(time.time()-st,2),flush=True)
 if r.returncode==10:subprocess.run(['python3',str(b/'synth.py'),'--decode',str(cnf.with_suffix('.json')),str(log)],check=True)
