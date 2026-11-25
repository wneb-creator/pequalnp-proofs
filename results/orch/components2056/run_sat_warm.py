import argparse,datetime,hashlib,json,subprocess,time
from pathlib import Path

p=argparse.ArgumentParser()
for option in ['cnf','mapping','library','phase','prefix']:p.add_argument('--'+option,required=True)
p.add_argument('--seconds',type=int,required=True)
a=p.parse_args();prefix=Path(a.prefix);root=Path(__file__).resolve().parent
exe=Path('/tmp/oec/pequalnp-pilot-121/toolchain/lean-4.36.0-linux/bin/cadical')
def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def timestamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
phase=json.loads(Path(a.phase).read_text());mask=Path(a.phase).parent/phase['mask_name']
assert phase['initial_phase'] is True and digest(a.cnf)==phase['warm_cnf_sha256']
assert digest(a.library)==phase['library_sha256'] and digest(a.mapping)==phase['mapping_sha256'] and digest(mask)==phase['mask_sha256']
files={'cnf':a.cnf,'mapping':a.mapping,'library':a.library,'phase':a.phase,'mask':mask,'encoder':root/'encode_reachable.py','phase_builder':root/'warm_phase.py','unrenamer':root/'unrename_model.py','decoder':root/'decode.py','runner':Path(__file__),'cadical':exe}
metadata={'started_utc':timestamp(),'duration_seconds':a.seconds,'initial_phase':True,'files':{k:{'path':str(v),'sha256':digest(v)} for k,v in files.items()},'status':'running'}
meta=prefix.with_suffix('.metadata.json');model=prefix.with_suffix('.sol');started=time.monotonic()
with prefix.with_suffix('.stdout').open('w') as out,prefix.with_suffix('.stderr').open('w') as err:
 child=subprocess.Popen([str(exe),'--phase=true','-t',str(a.seconds),'-w',str(model),a.cnf],stdout=out,stderr=err)
 metadata['child_pid']=child.pid;meta.write_text(json.dumps(metadata,indent=2)+'\n');print(json.dumps(metadata),flush=True)
 code=child.wait()
metadata.update(ended_utc=timestamp(),wall_seconds=time.monotonic()-started,returncode=code,status='completed')
if code==10:
 original_model=prefix.with_suffix('.unrenamed.sol')
 with prefix.with_suffix('.unrename.stdout').open('w') as out,prefix.with_suffix('.unrename.stderr').open('w') as err:
  result=subprocess.run(['python3',str(root/'unrename_model.py'),'--phase',a.phase,'--model',str(model),'--output',str(original_model)],stdout=out,stderr=err)
 metadata['unrename_returncode']=result.returncode
 if result.returncode==0:
  metadata['unrenamed_model_sha256']=digest(original_model)
  with prefix.with_suffix('.decode.stdout').open('w') as out,prefix.with_suffix('.decode.stderr').open('w') as err:
   result=subprocess.run(['python3',str(root/'decode.py'),'--library',a.library,'--data',str(root.parent/'patch2056/full-variable-data.json'),'--mapping',a.mapping,'--model',str(original_model),'--output',str(prefix.with_suffix('.candidate.json'))],stdout=out,stderr=err)
  metadata['decode_returncode']=result.returncode
  if result.returncode==0:metadata['candidate_sha256']=digest(prefix.with_suffix('.candidate.json'))
if model.exists():metadata['model_sha256']=digest(model)
meta.write_text(json.dumps(metadata,indent=2)+'\n');print(json.dumps(metadata),flush=True)
raise SystemExit(0 if code in (0,10,20) and metadata.get('unrename_returncode',0)==0 and metadata.get('decode_returncode',0)==0 else 1)
