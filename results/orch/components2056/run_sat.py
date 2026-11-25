import argparse
import datetime
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

p=argparse.ArgumentParser()
p.add_argument('--cnf',required=True);p.add_argument('--mapping',required=True)
p.add_argument('--library',required=True);p.add_argument('--prefix',required=True)
p.add_argument('--seconds',type=int,required=True)
a=p.parse_args();prefix=Path(a.prefix);root=Path(__file__).resolve().parent
exe=Path('/tmp/oec/pequalnp-pilot-121/toolchain/lean-4.36.0-linux/bin/cadical')
def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def timestamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
files={'cnf':a.cnf,'mapping':a.mapping,'library':a.library,'encoder':root/'encode.py','decoder':root/'decode.py','runner':Path(__file__),'cadical':exe}
metadata={'started_utc':timestamp(),'duration_seconds':a.seconds,'files':{k:{'path':str(v),'sha256':digest(v)} for k,v in files.items()},'status':'running'}
meta=prefix.with_suffix('.metadata.json');model=prefix.with_suffix('.sol');started=time.monotonic()
with prefix.with_suffix('.stdout').open('w') as out,prefix.with_suffix('.stderr').open('w') as err:
 child=subprocess.Popen([str(exe),'-t',str(a.seconds),'-w',str(model),a.cnf],stdout=out,stderr=err)
 metadata['child_pid']=child.pid;meta.write_text(json.dumps(metadata,indent=2)+'\n');print(json.dumps(metadata),flush=True)
 code=child.wait()
metadata.update(ended_utc=timestamp(),wall_seconds=time.monotonic()-started,returncode=code,status='completed')
if code==10:
 with prefix.with_suffix('.decode.stdout').open('w') as out,prefix.with_suffix('.decode.stderr').open('w') as err:
  decoder=subprocess.run(['python3',str(root/'decode.py'),'--library',a.library,'--data',str(root.parent/'patch2056/full-variable-data.json'),'--mapping',a.mapping,'--model',str(model),'--output',str(prefix.with_suffix('.candidate.json'))],stdout=out,stderr=err)
 metadata['decode_returncode']=decoder.returncode
 if decoder.returncode==0:metadata['candidate_sha256']=digest(prefix.with_suffix('.candidate.json'))
if model.exists():metadata['model_sha256']=digest(model)
meta.write_text(json.dumps(metadata,indent=2)+'\n');print(json.dumps(metadata),flush=True)
raise SystemExit(0 if code in (0,10,20) and metadata.get('decode_returncode',0)==0 else 1)
