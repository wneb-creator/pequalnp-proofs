from pathlib import Path
import subprocess,time,json
base=Path('/tmp/oec/pequalnp-pilot-78/toolchain')
start=time.monotonic();reason=None;high_since=None
limit=int(Path('/sys/fs/cgroup/memory.max').read_text())
with (base/'checker-smoke-retry.stdout').open('w') as out,(base/'checker-smoke-retry.stderr').open('w') as err,(base/'checker-smoke-retry.memory.jsonl').open('w') as log:
 p=subprocess.Popen(['.lake/build/bin/checklemma','PEqualNP.Defs',str(base/'smoke-statement.txt'),'check'],stdout=out,stderr=err)
 while p.poll() is None:
  elapsed=time.monotonic()-start
  current=int(Path('/sys/fs/cgroup/memory.current').read_text())
  events=dict(s.split() for s in Path('/sys/fs/cgroup/memory.events').read_text().splitlines())
  log.write(json.dumps({'seconds':round(elapsed,2),'bytes':current,'events':events})+'\n');log.flush()
  if current>limit*0.99:
   if high_since is None:high_since=time.monotonic()
  else:high_since=None
  if high_since is not None and time.monotonic()-high_since>60:reason='continuous memory saturation for 60 seconds'
  if elapsed>150:reason='150-second smoke deadline'
  if reason:
   p.terminate()
   try:p.wait(timeout=10)
   except subprocess.TimeoutExpired:p.kill();p.wait()
   break
  time.sleep(1)
 result={'exit':p.wait(),'seconds':round(time.monotonic()-start,2),'stopped_reason':reason}
 (base/'checker-smoke-retry.result.json').write_text(json.dumps(result)+'\n')
 print(json.dumps(result))
