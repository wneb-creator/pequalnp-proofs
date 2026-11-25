from pathlib import Path
import datetime,json,os,signal,subprocess,time

repo=Path('/workspace/pequalnp-proofs');scratch=Path('/tmp/oec/pequalnp-pilot-121/components2056')
reports=[]
for wanted in ['native','warm-check']:
 prefix=scratch/('v5-cancel-'+wanted)
 argv=['python3','results/orch/components2056/run_sat_warm_checked.py','--cnf',str(scratch/'v5-control64-warm.cnf'),'--original-cnf',str(scratch/'v5-control64.cnf'),'--mapping',str(scratch/'v5-control64.mapping.json'),'--library','results/orch/components2056/v5-library.json','--phase',str(scratch/'v5-control64-warm.phase.json'),'--prefix',str(prefix),'--seconds','30']
 metadata=prefix.with_suffix('.metadata.json');assert not metadata.exists()
 with prefix.with_suffix('.wrapper.stdout').open('w') as out,prefix.with_suffix('.wrapper.stderr').open('w') as err:
  proc=subprocess.Popen(argv,cwd=repo,stdout=out,stderr=err,start_new_session=True)
  deadline=time.monotonic()+20
  while True:
   assert proc.poll() is None,('wrapper exited before controlled cancellation',wanted)
   try:r=json.loads(metadata.read_text())
   except (FileNotFoundError,json.JSONDecodeError):r={}
   if r.get('stage')==wanted:break
   assert time.monotonic()<deadline,('control stage timeout',wanted)
   time.sleep(0.02)
  child=r['child_pid'];sent=datetime.datetime.now(datetime.timezone.utc).isoformat();os.kill(proc.pid,signal.SIGTERM)
  code=proc.wait(timeout=15)
 r=json.loads(metadata.read_text());assert code==143 and r['status']=='interrupted' and r['cancel_signal']==15
 try:os.kill(child,0)
 except ProcessLookupError:alive=False
 else:alive=True
 assert not alive and not prefix.with_suffix('.candidate.json').exists()
 reports.append({'phase':wanted,'sent_utc':sent,'wrapper_pid':proc.pid,'child_pid':child,'wrapper_returncode':code,'child_reaped':True,'metadata':r})
(scratch/'warm-cancellation-controls.json').write_text(json.dumps(reports,indent=2)+'\n')
print(json.dumps([{'phase':r['phase'],'returncode':r['wrapper_returncode'],'child_reaped':r['child_reaped']} for r in reports]))
