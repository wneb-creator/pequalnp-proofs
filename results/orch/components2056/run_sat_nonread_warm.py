import argparse,datetime,hashlib,json,os,signal,subprocess,time
from pathlib import Path

p=argparse.ArgumentParser()
for name in ['cnf','original-cnf','mapping','library','phase','prefix']:p.add_argument('--'+name,required=True)
p.add_argument('--seconds',type=int,required=True)
p.add_argument('--phase-builder',required=True)
p.add_argument('--appender-source',required=True)
p.add_argument('--stop-at-utc',required=True)
a=p.parse_args();prefix=Path(a.prefix);root=Path('/workspace/pequalnp-proofs/results/orch/components2056')
exe=Path('/tmp/oec/pequalnp-pilot-121/toolchain/lean-4.36.0-linux/bin/cadical')
def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def timestamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
phase=json.loads(Path(a.phase).read_text());mask=Path(a.phase).parent/phase['mask_name']
assert digest(a.phase_builder)==phase['source_sha256'] and digest(a.appender_source)==phase['appender_source_sha256']
assert phase['initial_phase'] is True and digest(a.cnf)==phase['warm_cnf_sha256']
assert digest(a.original_cnf)==phase['original_cnf_sha256'] and digest(a.mapping)==phase['mapping_sha256']
assert digest(a.library)==phase['library_sha256'] and digest(mask)==phase['mask_sha256']
files={'cnf':a.cnf,'original_cnf':a.original_cnf,'mapping':a.mapping,'library':a.library,'phase':a.phase,'mask':mask,'encoder':root/'encode_reachable.py','phase_builder':Path(a.phase_builder),'nonread_appender':Path(a.appender_source),'unrenamer':root/'unrename_model.py','clause_checker':root/'verify_cnf_model.py','decoder':root/'decode.py','runner':Path(__file__),'cadical':exe}
metadata={'started_utc':timestamp(),'duration_seconds':a.seconds,'initial_phase':True,'files':{k:{'path':str(v),'sha256':digest(v)} for k,v in files.items()},'status':'running'}
meta=prefix.with_suffix('.metadata.json');model=prefix.with_suffix('.sol');started=time.monotonic()
active=None;cancelled=None
def save():meta.write_text(json.dumps(metadata,indent=2)+'\n')
def forward(signum,frame):
 global cancelled
 cancelled=signum
 if active is not None and active.poll() is None:
  try:os.killpg(active.pid,signum)
  except ProcessLookupError:pass
old_handlers={sig:signal.signal(sig,forward) for sig in (signal.SIGTERM,signal.SIGINT)}
def run_child(stage,argv):
 global active
 if cancelled is not None:return -cancelled
 out_path=prefix.with_suffix('.stdout' if stage=='native' else '.'+stage+'.stdout')
 err_path=prefix.with_suffix('.stderr' if stage=='native' else '.'+stage+'.stderr')
 with out_path.open('w') as out,err_path.open('w') as err:
  active=subprocess.Popen(argv,stdout=out,stderr=err,start_new_session=True)
  if cancelled is not None:
   try:os.killpg(active.pid,cancelled)
   except ProcessLookupError:pass
  metadata.update(stage=stage,child_pid=active.pid)
  if stage=='native':metadata['native_child_pid']=active.pid
  save();code=active.wait();active=None
 metadata[stage+'_returncode']=code;save();return code
pipeline=0
try:
 deadline=datetime.datetime.fromisoformat(a.stop_at_utc);assert deadline.tzinfo is not None
 duration=min(a.seconds,int((deadline-datetime.datetime.now(datetime.timezone.utc)).total_seconds()));assert duration>0
 metadata.update(duration_requested_seconds=a.seconds,duration_seconds=duration,absolute_native_stop_utc=deadline.isoformat())
 native=run_child('native',[str(exe),'--phase=true','-t',str(duration),'-w',str(model),a.cnf])
 metadata['returncode']=native
 if native==10 and cancelled is None:
  original_model=prefix.with_suffix('.unrenamed.sol')
  stages=[
   ('warm-check',['python3',str(root/'verify_cnf_model.py'),'--cnf',a.cnf,'--model',str(model),'--output',str(prefix.with_suffix('.warm-check.json'))]),
   ('unrename',['python3',str(root/'unrename_model.py'),'--phase',a.phase,'--model',str(model),'--output',str(original_model)]),
   ('original-check',['python3',str(root/'verify_cnf_model.py'),'--cnf',a.original_cnf,'--model',str(original_model),'--output',str(prefix.with_suffix('.original-check.json'))]),
   ('decode',['python3',str(root/'decode.py'),'--library',a.library,'--data',str(root.parent/'patch2056/full-variable-data.json'),'--mapping',a.mapping,'--model',str(original_model),'--output',str(prefix.with_suffix('.candidate.json'))])]
  for stage,argv in stages:
   if cancelled is not None:break
   if run_child(stage,argv)!=0:pipeline=1;break
  if pipeline==0 and cancelled is None:
   metadata['candidate_sha256']=digest(prefix.with_suffix('.candidate.json'))
   metadata['unrenamed_model_sha256']=digest(original_model)
 elif native not in (0,20):pipeline=1
except BaseException as exc:
 pipeline=1;metadata['exception_type']=type(exc).__name__;raise
finally:
 if active is not None and active.poll() is None:
  try:os.killpg(active.pid,signal.SIGTERM)
  except ProcessLookupError:pass
  active.wait();active=None
 if model.exists():metadata['model_sha256']=digest(model)
 final_cancel=cancelled
 metadata.update(ended_utc=timestamp(),wall_seconds=time.monotonic()-started,status='interrupted' if final_cancel is not None else 'completed',cancel_signal=final_cancel)
 metadata['pipeline_returncode']=128+final_cancel if final_cancel is not None else pipeline
 save();print(json.dumps(metadata),flush=True)
 for sig,handler in old_handlers.items():signal.signal(sig,handler)
raise SystemExit(metadata['pipeline_returncode'])
