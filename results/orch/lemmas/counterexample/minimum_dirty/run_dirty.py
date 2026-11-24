import json,subprocess,sys,threading
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,as_completed
from datetime import datetime,timezone
base=Path(__file__).resolve().parent;ids=['g58672','g51809','g62497','g61969','g58129'];results=[];lock=threading.Lock()
def run(gid):
 with(base/(gid+'.run.log')).open('w')as f:p=subprocess.run([sys.executable,str(base/'solve_dirty.py'),'--id',gid,'--timeout','120'],stdout=f,stderr=subprocess.STDOUT)
 files=list(base.glob(gid+'_dirty_atmost*.json'));r=json.loads(files[0].read_text())if p.returncode==0 and files else {'id':gid,'result':'error','exitcode':p.returncode}
 if r['result']=='sat':
  with(base/(gid+'.diagnosis.log')).open('w')as f:subprocess.run([sys.executable,str(base/'diagnose.py'),str(files[0])],stdout=f,stderr=subprocess.STDOUT,check=True)
 with lock:
  results.append(r);(base/'results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(r),flush=True)
with ThreadPoolExecutor(max_workers=2)as ex:
 for f in as_completed([ex.submit(run,g)for g in ids]):f.result()
print('complete',datetime.now(timezone.utc).isoformat(),flush=True)
