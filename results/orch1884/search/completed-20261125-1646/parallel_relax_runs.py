import hashlib,json,os,signal,subprocess,time
from datetime import datetime,timezone
from pathlib import Path

s=Path('/tmp/oec/pequalnp-pilot-103/orch1884')
pidfile=s/'relax-batch-running.json'
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
for gates,extras in [(12,[21,273]),(13,[21,273,260])]:
    tag=f'relax{gates}-600-{23+len(extras)}rows'
    command=['python3',str(s/'cofactor_aux.py'),'--gates',str(gates),'--seconds','599',
        '--plain','--relax-negative','277','--productive','--primary-minimal',
        '--sat-preset','--seed','103','--tag',tag]
    for x in extras:command+=['--extra-negative',str(x)]
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
    'source_sha256':hashlib.sha256((s/'cofactor_aux.py').read_bytes()).hexdigest(),
    'scope':'Conditional shared-filter branch auxiliaries:12gates/25rows and13gates/26rows. Not the posted statement.',
    'freshness_not_required':True,'cases':[]}
for j in jobs:
    p=s/(j['tag']+'-result.json');entry={'tag':j['tag'],'exit':j['proc'].returncode,'command':j['command']}
    if p.exists():entry['result']=json.loads(p.read_text())
    else:entry['result_missing']=True
    report['cases'].append(entry)
(s/'relax-batch-report.json').write_text(json.dumps(report,indent=2)+'\n')
print('BATCH_FINISHED',json.dumps({'interrupted':stopped,'cases':[(j['tag'],j['proc'].returncode)for j in jobs]}),flush=True)
