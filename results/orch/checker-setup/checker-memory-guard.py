from pathlib import Path
import json,os,signal,subprocess,sys,time
prefix=Path(sys.argv[1]);command=sys.argv[2:]
started=time.monotonic();peak=0;stopped=None
with prefix.with_suffix('.stdout').open('wb') as out,prefix.with_suffix('.stderr').open('wb') as err:
 proc=subprocess.Popen(command,stdout=out,stderr=err,start_new_session=True)
 prefix.with_suffix('.pid').write_text(str(proc.pid)+'\n')
 while proc.poll() is None:
  values={line.split()[0]:int(line.split()[1]) for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines()}
  committed=sum(values.get(k,0) for k in ['anon','shmem','kernel']);peak=max(peak,committed)
  if committed>int(7.25*1024**3):stopped='non-reclaimable memory guard'
  if time.monotonic()-started>1800:stopped='30-minute runtime limit'
  if prefix.with_suffix('.STOP').exists():stopped='explicit stop request'
  if stopped:
   os.killpg(proc.pid,signal.SIGTERM)
   try:proc.wait(timeout=2)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
   break
  time.sleep(0.2)
 result={'command':command,'exit':proc.returncode,'seconds':time.monotonic()-started,'peak_nonreclaimable_bytes':peak,'stopped_by_guard':stopped}
 prefix.with_suffix('.result.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result),flush=True)
 raise SystemExit(0 if proc.returncode==0 else 1)
