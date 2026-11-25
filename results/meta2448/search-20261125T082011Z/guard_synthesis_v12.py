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
ap.add_argument('--encoder',choices=['synthesize.py','synthesize_v2.py','synthesize_v3.py','synthesize_v4.py','synthesize_v5.py','synthesize_v6.py','synthesize_v7.py','synthesize_v8.py','synthesize_v9.py','synthesize_v10.py','synthesize_v11.py'],default='synthesize.py')
ap.add_argument('arguments',nargs=argparse.REMAINDER)
args=ap.parse_args()
base=Path('/tmp/oec/pequalnp-pilot-62/meta2448')
stem=base/args.tag
assert not stem.with_suffix('.guard.json').exists()
assert args.arguments and args.arguments[0]=='--'
command=['python3',str(base/args.encoder)]+args.arguments[1:]+['--tag',args.tag]
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
    def live_group_members():
        members=[]
        for path in Path('/proc').iterdir():
            if not path.name.isdecimal():continue
            try:
                raw=(path/'stat').read_text()
                fields=raw[raw.rfind(')')+2:].split()
                if int(fields[2])==pid and fields[0]!='Z':
                    members.append({'pid':int(path.name),'start_ticks':int(fields[19])})
            except (FileNotFoundError,ProcessLookupError,PermissionError):pass
        return members
    cleanup_signals=[]
    def signal_group(sig):
        if not live_group_members():return
        leader=Path('/proc')/str(pid)/'stat'
        if leader.exists():
            raw=leader.read_text()
            assert int(raw[raw.rfind(')')+2:].split()[19])==record['process_start_ticks']
        try:os.killpg(pid,sig);cleanup_signals.append(signal.Signals(sig).name)
        except ProcessLookupError:pass
    def await_empty(seconds):
        end=time.monotonic()+seconds
        while live_group_members() and time.monotonic()<end:time.sleep(0.05)
        return not live_group_members()
    maximum=0;stopped=False
    while process.poll() is None:
        current=int(memory.read_text());maximum=max(maximum,current)
        if current>=6.5*1024**3:
            signal_group(signal.SIGINT);stopped=True
            if not await_empty(2):
                signal_group(signal.SIGTERM)
                if not await_empty(2):
                    signal_group(signal.SIGKILL);await_empty(2)
            break
        time.sleep(0.25)
    if live_group_members():
        signal_group(signal.SIGTERM)
        if not await_empty(2):signal_group(signal.SIGKILL);await_empty(2)
    exit_code=process.wait()
    final_members=live_group_members()
record.update({'wrapper_child_exit':exit_code,'shared_memory_guard_stop':stopped,
               'maximum_shared_memory_bytes':maximum,'cleanup_signals':cleanup_signals,
               'live_group_members_after_cleanup':final_members,'ended_utc':datetime.now(timezone.utc).isoformat()})
stem.with_suffix('.guard-status.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
