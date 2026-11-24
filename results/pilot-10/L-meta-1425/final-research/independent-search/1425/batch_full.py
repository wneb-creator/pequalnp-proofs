import concurrent.futures,json,subprocess,sys,time
from pathlib import Path
root=Path(__file__).parent
Ts=[0xe8a8a8a8,0xe8a8e888,0xe8e8e880,0xeaa8a888,0xeaa8c888,0xeaa8e880,0xeaaac880,0xeac0e8c0,0xeac8e0c0,0xeac8e880]
jobs=[(i,Ts[i],b,'full') for i,b in [(2,7),(3,8),(5,8),(9,8),(1,6),(4,6),(6,6)]]
def run(job):
 i,T,b,m=job;prefix=root/f't{i}-{m}{b}'
 with prefix.with_suffix('.stdout').open('w') as out,prefix.with_suffix('.stderr').open('w') as err:
  p=subprocess.run([sys.executable,str(root/'synthesize_truth_full.py'),hex(T),str(b),m,str(prefix),'180000'],stdout=out,stderr=err)
 d=json.loads(prefix.with_suffix('.result.json').read_text()) if prefix.with_suffix('.result.json').exists() else {'result':'error'}
 print(json.dumps({'i':i,'T':hex(T),'budget':b,'mode':m,'exit':p.returncode,**{k:d[k] for k in ['result','seconds','used'] if k in d}}),flush=True)
 return d
with concurrent.futures.ThreadPoolExecutor(max_workers=1) as pool:results=list(pool.map(run,jobs))
(root/'batch-full-results.json').write_text(json.dumps(results,indent=2)+'\n')
