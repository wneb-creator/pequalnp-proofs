import argparse,json,subprocess,sys,time
from pathlib import Path
from datetime import datetime,timezone
p=argparse.ArgumentParser();p.add_argument('--gates',type=int,default=7);p.add_argument('--min-not',type=int,default=0);p.add_argument('--max-not',type=int,default=0);p.add_argument('--timeout',type=int,default=120000);p.add_argument('--rounds',type=int,default=2);a=p.parse_args()
s=Path('/tmp/oec/pequalnp-pilot-92')
for i in range(15):
 prefix=s/('search-prefix-orbit-'+str(i)+'.json')
 log=s/('search-template-g'+str(a.gates)+'-orbit'+str(i)+'.log')
 args=[sys.executable,str(s/'search-z3-template.py'),'--gates',str(a.gates),'--prefix',str(prefix),'--min-not',str(a.min_not),'--max-not',str(a.max_not),'--critical','--allow-redundant','--timeout',str(a.timeout),'--rounds',str(a.rounds)]
 print(datetime.now(timezone.utc).isoformat(),'start orbit',i,flush=True)
 start=time.time()
 with log.open('w') as f:r=subprocess.run(args,stdout=f,stderr=subprocess.STDOUT)
 text=log.read_text()
 print(datetime.now(timezone.utc).isoformat(),'end orbit',i,'return',r.returncode,'elapsed',time.time()-start,'WITNESS' if '\nWITNESS\n' in text else 'UNSAT' if 'UNSAT for shard constraints' in text else 'UNKNOWN',flush=True)
 if r.returncode!=0 or '\nWITNESS\n' in text:break
