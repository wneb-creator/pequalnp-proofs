import argparse
from datetime import datetime,timezone
import json
import os
from pathlib import Path
import signal
import subprocess
import time

ap=argparse.ArgumentParser()
ap.add_argument('--tag',required=True)
ap.add_argument('arguments',nargs=argparse.REMAINDER)
args=ap.parse_args()
base=Path('/tmp/oec/pequalnp-pilot-62/meta2448')
stem=base/args.tag
assert not stem.with_suffix('.guard.json').exists()
assert args.arguments and args.arguments[0]=='--'
command=['python3',str(base/'synthesize.py')]+args.arguments[1:]+['--tag',args.tag]
memory=Path('/sys/fs/cgroup/memory.current')
assert int(memory.read_text())<4*1024**3
with stem.with_suffix('.log').open('w') as log:
    process=subprocess.Popen(command,cwd=base,stdout=log,stderr=subprocess.STDOUT,process_group=0)
    pid=process.pid
    stat=(Path('/proc')/str(pid)/'stat').read_text()
    record={'command':command,'pid':pid,'owned_process_group':pid,
            'process_start_ticks':int(stat[stat.rfind(')')+2:].split()[19]),
            'started_utc':datetime.now(timezone.utc).isoformat(),
            'synthesis_address_space_limit_bytes':1024**3,
            'shared_stop_limit_bytes':int(6.5*1024**3)}
    stem.with_suffix('.guard.json').write_text(json.dumps(record,indent=2)+'\n')
    maximum=0;stopped=False
    while process.poll() is None:
        current=int(memory.read_text());maximum=max(maximum,current)
        if current>=6.5*1024**3:
            os.killpg(pid,signal.SIGINT);stopped=True
            try:process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                os.killpg(pid,signal.SIGTERM)
                try:process.wait(timeout=2)
                except subprocess.TimeoutExpired:os.killpg(pid,signal.SIGKILL)
            break
        time.sleep(0.25)
    exit_code=process.wait()
record.update({'wrapper_child_exit':exit_code,'shared_memory_guard_stop':stopped,
               'maximum_shared_memory_bytes':maximum,'ended_utc':datetime.now(timezone.utc).isoformat()})
stem.with_suffix('.guard-status.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
