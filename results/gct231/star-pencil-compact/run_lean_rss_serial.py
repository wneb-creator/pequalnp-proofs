"""Run Lean with full logs, a wall deadline, and sampled process-group RSS cap.

Lean maps large olean files, so an address-space cap can reject imports despite
small resident memory. The RSS cap is sampled every half second, not a kernel
hard memory limit. Only the isolated child process group is terminated.
"""
import argparse
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('input')
p.add_argument('prefix')
p.add_argument('--seconds',type=int,default=180)
p.add_argument('--memory-mib',type=int,default=6144)
a = p.parse_args()
prefix = Path(a.prefix)
def limits():
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start = time.monotonic()
peak = 0
reason = None
with prefix.with_suffix('.log').open('w') as out:
    child = subprocess.Popen(['lake','env','lean','--threads=1',a.input],stdout=out,stderr=subprocess.STDOUT,
                             preexec_fn=limits,start_new_session=True)
    while child.poll() is None:
        measured = subprocess.run(['ps','-o','rss=','--sid',str(child.pid)],capture_output=True,text=True)
        rss = sum(int(value) for value in measured.stdout.split()) if measured.returncode == 0 else 0
        peak = max(peak,rss)
        if time.monotonic()-start > a.seconds:
            reason = 'UNKNOWN_TIME_LIMIT'
        elif rss > a.memory_mib*1024:
            reason = 'UNKNOWN_RESIDENT_MEMORY_LIMIT'
        if reason:
            os.killpg(child.pid,signal.SIGTERM)
            try:
                child.wait(timeout=3)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid,signal.SIGKILL)
                child.wait()
            break
        time.sleep(0.5)
result = {'status':reason or ('PASS' if child.returncode == 0 else 'FAIL'),
          'returncode':child.returncode,'wall_seconds':time.monotonic()-start,
          'seconds_limit':a.seconds,'resident_memory_mib_limit':a.memory_mib,
          'peak_group_rss_kib':peak,'rss_sample_seconds':0.5,'input':a.input}
prefix.with_suffix('.run.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
