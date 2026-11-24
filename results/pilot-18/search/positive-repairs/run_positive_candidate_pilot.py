"""Short candidate-only cover neighborhoods; never an exhaustion claim."""
import datetime, hashlib, json, os, re, resource, signal, subprocess, time
from pathlib import Path

ROOT=Path('/tmp/oec/pequalnp-pilot-18')
FAMILY=ROOT/'orch/S02/rescheduled-family'
OUT=ROOT/'positive-candidate-pilot'
SOLVER=ROOT/'solver/kissat-4.0.4-linux-amd64'
VALIDATOR=ROOT/'lean-setup/validate_sat_candidate.py'
assert hashlib.sha256(SOLVER.read_bytes()).hexdigest()=='21da5d984e38b74f620f14c62442f834f27b9158decdb722540d97f98aac93a1'
assert hashlib.sha256(VALIDATOR.read_bytes()).hexdigest()=='b807c1a580ce1fa49da51d859e6bc5d94bab2f9f0cd359c35cef35686f826529'
queue=[]
for source_name in ['positive-best3-family','positive-best4-family']:
    source_dir=ROOT/'orch/S02'/source_name
    manifest=json.loads((source_dir/'family.json').read_text())
    assert manifest['complete'] and len(manifest['cases'])==2
    assert manifest['program_sha256']=='7552f3d344d4e34a6f681b116b5ec748e032b2000315dfc9527c77f8de2bdb6b'
    item=next(x.copy() for x in manifest['cases'] if x['case']=='distance-k03')
    item['case']=source_name+'-distance-k03'
    item['source_cnf']=str(source_dir/'distance-k03.cnf')
    queue.append(item)
case_paths={x['case']:Path(x['source_cnf']) for x in queue}
OUT.mkdir(exist_ok=False)
(OUT/'worker-limit.txt').write_text('1\n')
state={'scope':'Candidate-only neighborhoods; no global or assigned-shard exhaustion.',
       'started':datetime.datetime.now(datetime.timezone.utc).isoformat(),'cases':{}}
active={};stopping=False

def save():
    p=OUT/'portfolio.json.tmp';p.write_text(json.dumps(state,indent=2)+'\n');p.replace(OUT/'portfolio.json')

def signal_stop(sig,frame):
    global stopping
    stopping=True

def limits():
    resource.setrlimit(resource.RLIMIT_AS,(1000*1024**2,1000*1024**2))

def stop_active(reason):
    for name,(proc,a,b,started) in active.items():
        if proc.poll() is None:
            try:os.killpg(proc.pid,signal.SIGTERM)
            except ProcessLookupError:pass
        state['cases'][name]['interrupted']=reason
    for name,(proc,a,b,started) in active.items():
        try:proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            try:os.killpg(proc.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            proc.wait()
        a.close();b.close();state['cases'][name]['exit_code']=proc.returncode
    active.clear();save()

signal.signal(signal.SIGTERM,signal_stop);signal.signal(signal.SIGINT,signal_stop)
try:
    while queue or active:
        if stopping or (ROOT/'DESK_ERROR.response').exists():
            stop_active('Coordinator stop or desk error');break
        workers=int((OUT/'worker-limit.txt').read_text());assert 1<=workers<=2
        while queue and len(active)<workers:
            item=queue.pop(0);name=item['case'];assert re.fullmatch(r'positive-best[34]-family-distance-k03',name)
            cnf=case_paths[name]
            assert hashlib.sha256(cnf.read_bytes()).hexdigest()==item['cnf_sha256']
            assert hashlib.sha256(cnf.with_suffix('.json').read_bytes()).hexdigest()==item['metadata_sha256']
            command=[str(SOLVER),'--sat','--time=20',str(cnf)]
            a=(OUT/(name+'.stdout')).open('x');b=(OUT/(name+'.stderr')).open('x')
            proc=subprocess.Popen(command,stdout=a,stderr=b,start_new_session=True,preexec_fn=limits)
            active[name]=(proc,a,b,time.monotonic())
            state['cases'][name]={'pid':proc.pid,'cnf_sha256':item['cnf_sha256'],'budget':item['budget'],
                'started':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':command}
            save();print('START',name,proc.pid,flush=True)
        for name,(proc,a,b,started) in list(active.items()):
            if proc.poll() is None:
                if time.monotonic()-started>30:
                    state['error']='Solver exceeded 30-second outer limit';stopping=True
                continue
            code=proc.wait();a.close();b.close();del active[name]
            status=[line for line in (OUT/(name+'.stdout')).read_text().splitlines() if line.startswith('s ')]
            state['cases'][name].update(exit_code=code,status_lines=status,elapsed_seconds=time.monotonic()-started)
            save();print('FINISH',name,code,status,flush=True)
            if code==10 or status==['s SATISFIABLE']:
                stop_active('Candidate found; all-input validation required')
                cnf=case_paths[name]
                with (OUT/(name+'.validation.stdout')).open('x') as va,(OUT/(name+'.validation.stderr')).open('x') as vb:
                    checked=subprocess.run(['python',str(VALIDATOR),str(cnf),str(OUT/(name+'.stdout'))],stdout=va,stderr=vb,timeout=120)
                state['candidate']={'case':name,'validator_exit':checked.returncode,
                    'report':str(cnf.with_suffix('.validated.json')),'requires_Lean_proof':True}
                stopping=True;save();print('CANDIDATE',name,'validator_exit',checked.returncode,flush=True);break
            if code not in (0,20):
                state['error']=f'Unexpected solver exit {code} for {name}';stopping=True;save();break
        time.sleep(0.2)
finally:
    if active:stop_active('Controller exiting')
    state['finished']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
