import subprocess,json,time,pathlib,os,sys
from datetime import datetime,timezone
s=pathlib.Path(__file__).resolve().parent
for p in json.loads((s/'fresh-meta3773-five-handover.json').read_text())['children']:
 while True:
  try:
   os.kill(p,0)
   status=subprocess.run(['ps','-o','stat=','-p',str(p)],capture_output=True,text=True).stdout.strip()
   if not status or status.startswith('Z'):break
   time.sleep(0.3)
  except ProcessLookupError:break
schedule=[(62,2),(31,3),(55,3),(62,1),(62,0),(62,1),(62,0),(31,2),(62,1),(62,0),(47,2),(62,1),(62,0),(55,2),(62,1),(62,0),(31,2),(31,1),(31,0),(47,2),(55,2)]
for m,d in schedule:
 if datetime.now(timezone.utc).strftime('%H:%M:%S')>='14:29:05':break
 stem=f'fresh-meta3773-five-1-{m}-{d}';p=s/(stem+'-progress.json');j=json.loads(p.read_text())if p.exists()else{}
 if j.get('tested',-1)==j.get('total',-2)or j.get('hits'):continue
 log=s/(stem+'-s'+str(time.time_ns())+'.log');print(m,d,log.name,flush=True)
 with log.open('wb')as o:r=subprocess.run(['timeout','19s',sys.executable,('fresh_meta3773_five_checkpoint.py' if d<2 else 'fresh_meta3773_five_sixteen.py'),'1',str(m),str(d)],cwd=s,stdout=o,stderr=subprocess.STDOUT)
 if r.returncode not in (0,124):raise RuntimeError((r.returncode,log.name))
