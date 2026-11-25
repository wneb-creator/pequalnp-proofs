import json
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
job=Path('/tmp/oec/pequalnp-pilot-107')
repo=Path('/workspace/pequalnp-proofs')
url='https://pequalnp.com/desk/next?handle=wneb-creator&another=1&hard=1'
state=json.loads((job/'desk-poller-state.json').read_text())
last=datetime.fromisoformat(state['last_utc']).timestamp()
stop_at=datetime(2026,11,25,19,49,56,tzinfo=timezone.utc).timestamp()
null_count=state['null_count']
attempt=state['attempts_in_poller']
while time.time()<stop_at and not (job/'desk-poller-stop').exists():
    if time.time()<last+240:
        time.sleep(5)
        continue
    attempt+=1
    stamp=datetime.now(timezone.utc).isoformat()
    r=subprocess.run(['curl','-s',url],capture_output=True,text=True,cwd=repo)
    name='desk-poll-'+str(attempt).zfill(3)
    (job/(name+'.json')).write_text(r.stdout)
    (job/(name+'.stderr')).write_text(r.stderr)
    with (job/'desk-log.txt').open('a') as f:f.write('\n'+stamp+' desk next poll\n'+r.stdout+'\n'+r.stderr)
    last=time.time()
    try:d=json.loads(r.stdout)
    except (ValueError,TypeError):d=None
    if r.returncode!=0 or not isinstance(d,dict) or d.get('error'):
        diag=subprocess.run(['curl','-si',url],capture_output=True,text=True,cwd=repo)
        (job/'desk-poller-error-response.txt').write_text(diag.stdout+diag.stderr)
        (job/'desk-poller-error').write_text(stamp+'\n')
        with (job/'desk-log.txt').open('a') as f:f.write(stamp+' DIAGNOSTIC curl -si\n'+diag.stdout+diag.stderr+'\n')
        print('DESK ERROR\n'+diag.stdout+diag.stderr,flush=True)
        sys.exit(42)
    if isinstance(d.get('gap'),dict) and isinstance(d.get('lease'),dict):
        (job/'desk-poller-acquired.json').write_text(r.stdout)
        print(stamp+' GAP ACQUIRED '+d['gap'].get('id','unknown')+'; root must inspect and start renewal',flush=True)
        sys.exit(0)
    if d.get('gap') is None:
        null_count+=1
        note=d.get('note',d.get('message',''))
        state={'last_utc':stamp,'null_count':null_count,'last_note':note,'attempts_in_poller':attempt,'response_file':name+'.json'}
        (job/'desk-poller-state.json').write_text(json.dumps(state,indent=2)+'\n')
        print(stamp+' NULL '+str(null_count)+' '+note,flush=True)
        if note.lower().startswith(('you already hold a gap', 'you already hold l-', 'you hold ')) or 'most one handle may hold' in note.lower():
            (job/'desk-poller-holding-message.json').write_text(r.stdout)
            sys.exit(43)
        continue
    (job/'desk-poller-unexpected.json').write_text(r.stdout)
    print(stamp+' UNEXPECTED RESPONSE; root must inspect',flush=True)
    sys.exit(44)
(job/'desk-poller-finished').write_text(datetime.now(timezone.utc).isoformat()+'\n')
print('POLLER FINISHED; null_count='+str(null_count),flush=True)
