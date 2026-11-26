import argparse,json,resource,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('--label',required=True)
p.add_argument('--directory',type=Path,required=True)
p.add_argument('--cwd',type=Path,required=True)
p.add_argument('command',nargs=argparse.REMAINDER)
a=p.parse_args()
cmd=a.command[1:] if a.command[:1]==['--'] else a.command
if not cmd: p.error('command required')
if not a.label.replace('_','').replace('-','').isalnum(): p.error('invalid label')
a.directory.mkdir(parents=True,exist_ok=True)
t=time.perf_counter()
with (a.directory/(a.label+'.stdout')).open('w') as out,(a.directory/(a.label+'.stderr')).open('w') as err:
    r=subprocess.run(cmd,cwd=a.cwd,stdout=out,stderr=err)
u=resource.getrusage(resource.RUSAGE_CHILDREN)
d=dict(exit=r.returncode,wall_seconds=time.perf_counter()-t,user_seconds=u.ru_utime,system_seconds=u.ru_stime,maxrss_kib=u.ru_maxrss)
(a.directory/(a.label+'.resources.json')).write_text(json.dumps(d,indent=2)+'\n')
print(json.dumps(d),flush=True)
raise SystemExit(r.returncode)
