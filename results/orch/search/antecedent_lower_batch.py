import json,subprocess,sys,time
from pathlib import Path
r=Path('/tmp/oec/pequalnp-pilot-176');d=json.loads((r/'antecedent-graphs6.json').read_text())
for name,g in d.items():
 for k in range(5,g['bound']):
    argv=[sys.executable,str(r/'antecedent_search.py'),'--n','6','--gates',str(k),'--junk','2','--edges',','.join(str(a)+'-'+str(b) for a,b in g['edges']),'--timeout','30000']
    t=time.time();tag='twojunk-g6-'+name+'-k'+str(k)
    with (r/(tag+'.stdout')).open('w') as out,(r/(tag+'.stderr')).open('w') as err:
        x=subprocess.run(argv,stdout=out,stderr=err)
    print(name,k,x.returncode,round(time.time()-t,2),(r/(tag+'.stdout')).read_text(),flush=True)
