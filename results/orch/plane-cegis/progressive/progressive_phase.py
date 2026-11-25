import datetime,json,os,shutil,signal,subprocess,sys,time
from pathlib import Path

base=Path(__file__).resolve().parent
out=base/'progressive'
out.mkdir(exist_ok=True)
started=time.monotonic();deadline=started+1200
current=None;interrupted=None;events=[]
def event(kind,**details):
 record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-started,'event':kind,**details}
 events.append(record)
 with (out/'events.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
 print(json.dumps(record),flush=True)
def stop(sig,frame):
 global interrupted
 interrupted=sig
 if current is not None and current.poll() is None:
  try:current.send_signal(sig)
  except ProcessLookupError:pass
signal.signal(signal.SIGTERM,stop)
shutil.copyfile(base/'rows-000.json',out/'rows-000.json')
(out/'phase-process.json').write_text(json.dumps({'driver_pid':os.getpid(),'wall_budget_seconds':1200,'native_cap_seconds':300})+'\n')
event('phase_start',wall_budget_seconds=1200,native_cap_seconds=300,batch_size=2,initial_rows=54)
final='no query run'
for iteration in range(1000):
 if interrupted is not None:final='interrupted';break
 remaining=deadline-time.monotonic()
 if remaining<=8:final='wall budget exhausted';break
 rowfile=out/f'rows-{iteration:03d}.json';rows=json.loads(rowfile.read_text());prefix=out/f'query-{iteration:03d}'
 seconds=min(10 if iteration==0 else 300,max(1,int(remaining)-8))
 command=[sys.executable,str(base/'direct_cnf_progressive.py'),'--data',str(base/'plane2056-data.json'),'--rows',str(rowfile),'--size','63','--seconds',str(seconds),'--prefix',str(prefix)]
 if iteration==0:command+=['--fixed-gates',str(base/'seed25-padded63-gates.json')]
 prefix.with_suffix('.command.json').write_text(json.dumps(command,indent=2)+'\n')
 event('query_start',iteration=iteration,rows=len(rows),native_seconds=seconds,fixed_initial_seed=iteration==0)
 with prefix.with_suffix('.wrapper.stdout').open('w') as stdout,prefix.with_suffix('.wrapper.stderr').open('w') as stderr:
  current=subprocess.Popen(command,stdout=stdout,stderr=stderr)
  try:current.wait(timeout=max(1,deadline-time.monotonic()))
  except subprocess.TimeoutExpired:
   event('query_wall_timeout',iteration=iteration)
   current.send_signal(signal.SIGTERM)
   try:current.wait(timeout=5)
   except subprocess.TimeoutExpired:
    process_file=prefix.with_suffix('.process.json')
    if process_file.exists():
     ids=json.loads(process_file.read_text())
     try:os.killpg(ids['solver_pid'],signal.SIGKILL)
     except ProcessLookupError:pass
    current.kill();current.wait()
   final='wall budget exhausted during query';break
 exit_code=current.returncode;current=None
 if interrupted is not None:final='interrupted';break
 if exit_code!=0:
  event('query_wrapper_error',iteration=iteration,exit_code=exit_code);final='query wrapper error';break
 resultfile=prefix.with_suffix('.json')
 if not resultfile.exists():event('missing_result',iteration=iteration);final='missing result';break
 result=json.loads(resultfile.read_text())
 assert isinstance(result,dict) and 'exit_code' in result and 'status' in result
 event('query_result',iteration=iteration,rows=len(rows),status=result['status'],solver_exit_code=result['exit_code'],clauses=result['clauses'])
 if result['exit_code']!=10:final=result['status'];break
 nextrows=out/f'rows-{iteration+1:03d}.json';report=out/f'refine-{iteration:03d}.json'
 command=[sys.executable,str(base/'refine.py'),'--data',str(base/'plane2056-data.json'),'--rows',str(rowfile),'--model',str(resultfile),'--output-rows',str(nextrows),'--report',str(report),'--batch','2']
 with (out/f'refine-{iteration:03d}.stdout').open('w') as stdout,(out/f'refine-{iteration:03d}.stderr').open('w') as stderr:
  checked=subprocess.run(command,stdout=stdout,stderr=stderr)
 if checked.returncode!=0:event('refinement_error',iteration=iteration,exit_code=checked.returncode);final='refinement error';break
 refinement=json.loads(report.read_text())
 event('model_checked',iteration=iteration,rows=len(rows),full_boundary_rows=refinement['tested_rows'],violations=refinement['violations'],new_rows=refinement['updated_rows'],selected_rows=refinement['selected_rows'])
 if refinement['violations']==0:
  final='full-boundary candidate found; Lean verification required';event('candidate',model=str(resultfile));break
summary={'status':final,'elapsed_seconds':time.monotonic()-started,'events':events,'interrupted':interrupted}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
event('phase_end',status=final)
if interrupted is not None:raise SystemExit(128+interrupted)
