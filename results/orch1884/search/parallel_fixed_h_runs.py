import hashlib,json,os,signal,subprocess,time
from datetime import datetime,timezone
from pathlib import Path

s=Path('/tmp/oec/pequalnp-pilot-103/orch1884')
pidfile=s/'h5-direct-batch-running.json'
jobs=[];stopped=False
def snapshot():
    pidfile.write_text(json.dumps({'wrapper_pid':os.getpid(),'stopping':stopped,
        'updated_at':datetime.now(timezone.utc).isoformat(),
        'jobs':[{'tag':j['tag'],'case_pid':j['proc'].pid,'exit':j['proc'].poll()}for j in jobs]},indent=2)+'\n')
def terminate(sig,frame):
    global stopped
    stopped=True
    for j in jobs:
        if j['proc'].poll() is None:
            try:os.killpg(j['proc'].pid,signal.SIGTERM)
            except ProcessLookupError:pass
    snapshot()
signal.signal(signal.SIGTERM,terminate)
signal.signal(signal.SIGINT,terminate)
started=datetime.now(timezone.utc).isoformat()
for label in ['Astar','Vpartial']:
    tag='h5-direct600-'+label
    command=['python3',str(s/'free_not_cnf.py'),'--gates','18','--max-nots','0',
        '--seconds','600','--rail-readers','--fresh','--primary-minimal','--positive-guard',
        '--pin',str(s/f'h5-direct-{label}-seed18.json'),'--mutable','6,7,8,9,10,11,12,13,14,15,16,17',
        '--sat-preset','--seed','103','--tag',tag]
    out=(s/(tag+'.log')).open('w')
    proc=subprocess.Popen(command,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
    jobs.append({'tag':tag,'proc':proc,'out':out,'command':command,'reported':False})
    snapshot();print('STARTED',tag,proc.pid,flush=True)
while any(j['proc'].poll() is None for j in jobs):
    for j in jobs:
        if not j['reported'] and j['proc'].poll() is not None:
            j['reported']=True;print('FINISHED',j['tag'],j['proc'].returncode,flush=True);snapshot()
    time.sleep(1)
for j in jobs:j['out'].close()
snapshot()
report={'started_at':started,'finished_at':datetime.now(timezone.utc).isoformat(),'interrupted':stopped,
    'source_sha256':hashlib.sha256((s/'free_not_cnf.py').read_bytes()).hexdigest(),
    'scope':'Fixed five-gate H cone and positive rail OR as the first six gates; twelve remaining gates free.',
    'cases':[]}
for j in jobs:
    p=s/(j['tag']+'-result.json');entry={'tag':j['tag'],'exit':j['proc'].returncode,'command':j['command']}
    if p.exists():entry['result']=json.loads(p.read_text())
    else:entry['result_missing']=True
    report['cases'].append(entry)
(s/'h5-direct-batch-report.json').write_text(json.dumps(report,indent=2)+'\n')
print('BATCH_FINISHED',json.dumps({'interrupted':stopped,'cases':[(j['tag'],j['proc'].returncode)for j in jobs]}),flush=True)
