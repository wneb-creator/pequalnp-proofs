import subprocess,json,time
from pathlib import Path
b=Path('/tmp/oec/pequalnp-pilot-31/search')
for path in ['/tmp/oec/pequalnp-pilot-31/random/near_one/near-8-30.json','/tmp/oec/pequalnp-pilot-31/random/near-8-6.json','/tmp/oec/pequalnp-pilot-31/random/near-8-11.json','/tmp/oec/pequalnp-pilot-31/random/near-8-4.json']:
 gp=Path(path);d=json.loads(gp.read_text());name='local-n8-'+gp.stem.split('-')[-1];cnf=b/(name+'.cnf');log=b/(name+'.log')
 subprocess.run(['python3',str(b/'synth.py'),'--n','8','--e',str(len(d['edges'])),'--t',str(d['tau']),'--graph',str(gp),'--template',str(gp),'--distance','4','--out',str(cnf)],check=True)
 st=time.time()
 with log.open('w')as f:r=subprocess.run([str(b/'kissat/build/kissat'),'--time=120',str(cnf)],stdout=f,stderr=subprocess.STDOUT)
 print(name,'returncode',r.returncode,'seconds',round(time.time()-st,2),flush=True)
 if r.returncode==10:subprocess.run(['python3',str(b/'synth.py'),'--decode',str(cnf.with_suffix('.json')),str(log)],check=True)
