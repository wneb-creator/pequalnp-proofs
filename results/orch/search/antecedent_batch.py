import json,subprocess,sys,time
from pathlib import Path
r=Path('/tmp/oec/pequalnp-pilot-176');d=json.loads((r/'antecedent-graphs6.json').read_text())
for name,g in d.items():
    if name=='238': continue
    argv=[sys.executable,str(r/'antecedent_search.py'),'--n','6','--gates',str(g['bound']),'--junk','2','--edges',','.join(str(a)+'-'+str(b) for a,b in g['edges']),'--timeout','60000']
    t=time.time()
    with (r/('twojunk-g6-'+name+'.stdout')).open('w') as out,(r/('twojunk-g6-'+name+'.stderr')).open('w') as err:
        x=subprocess.run(argv,stdout=out,stderr=err)
    print(name,x.returncode,round(time.time()-t,2),(r/('twojunk-g6-'+name+'.stdout')).read_text(),flush=True)
