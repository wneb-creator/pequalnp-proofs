import argparse
from datetime import datetime,timezone
import json
import os
from pathlib import Path
import signal
import time

ap=argparse.ArgumentParser();ap.add_argument('tags',nargs='+');args=ap.parse_args()
base=Path('/tmp/oec/pequalnp-pilot-62/meta2448')
records=[]
for tag in args.tags:
    assert '/' not in tag and tag.startswith('petersen')
    record=json.loads((base/(tag+'.guard.json')).read_text())
    assert record['owned_process_group']==record['pid'] and record['pid']>0
    record.update({'tag':tag,'reattached_utc':datetime.now(timezone.utc).isoformat(),'cleanup_signals':[],'maximum_shared_memory_bytes':0})
    records.append(record)

def members(record):
    result=[]
    for path in Path('/proc').iterdir():
        if not path.name.isdecimal():continue
        try:
            raw=(path/'stat').read_text();fields=raw[raw.rfind(')')+2:].split()
            if int(fields[2])==record['pid'] and fields[0]!='Z':
                result.append({'pid':int(path.name),'start_ticks':int(fields[19])})
        except (FileNotFoundError,ProcessLookupError,PermissionError):pass
    return result

def validate(record):
    leader=Path('/proc')/str(record['pid'])/'stat'
    if leader.exists():
        raw=leader.read_text();assert int(raw[raw.rfind(')')+2:].split()[19])==record['process_start_ticks']

def send(record,sig):
    if not members(record):return
    validate(record)
    try:os.killpg(record['pid'],sig);record['cleanup_signals'].append(signal.Signals(sig).name)
    except ProcessLookupError:pass

def empty_after(record,seconds):
    end=time.monotonic()+seconds
    while members(record) and time.monotonic()<end:time.sleep(0.05)
    return not members(record)

for record in records:validate(record)
print(json.dumps({'started':datetime.now(timezone.utc).isoformat(),'groups':[r['pid'] for r in records]}),flush=True)
while records:
    current=int(Path('/sys/fs/cgroup/memory.current').read_text())
    for record in records[:]:
        record['maximum_shared_memory_bytes']=max(record['maximum_shared_memory_bytes'],current)
        if members(record) and current>=6.5*1024**3:
            record['shared_memory_guard_stop']=True
            send(record,signal.SIGINT)
            if not empty_after(record,2):
                send(record,signal.SIGTERM)
                if not empty_after(record,2):send(record,signal.SIGKILL);empty_after(record,2)
        if not members(record):
            record.setdefault('shared_memory_guard_stop',False)
            record.update({'ended_utc':datetime.now(timezone.utc).isoformat(),'live_group_members_after_cleanup':members(record),'scope':'Reattached monitor only; model/solver status remains in original status file.'})
            (base/(record['tag']+'.recovery-guard-status.json')).write_text(json.dumps(record,indent=2)+'\n')
            print(json.dumps(record),flush=True);records.remove(record)
    time.sleep(0.25)
