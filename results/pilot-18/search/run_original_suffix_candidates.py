"""Candidate-only diversification; UNKNOWN and uncertified UNSAT prove nothing."""
import datetime, hashlib, json, os, resource, signal, subprocess, time
from pathlib import Path

ROOT = Path('/tmp/oec/pequalnp-pilot-18')
CNFS = ROOT/'original-suffix4'
OUT = ROOT/'original-suffix-candidates'
SOLVER = ROOT/'solver/kissat-4.0.4-linux-amd64'
FAMILY = json.loads((CNFS/'family.json').read_text())
assert hashlib.sha256((CNFS/'family.json').read_bytes()).hexdigest()=='8b690331982b60dcd6644e02f078dd548e2087e0175efd5ca515f5f760cc9c0d'
assert hashlib.sha256(SOLVER.read_bytes()).hexdigest()=='21da5d984e38b74f620f14c62442f834f27b9158decdb722540d97f98aac93a1'
CASES = ['suffix-AAAO','suffix-AAOA','suffix-AOAA','suffix-AAAA']
EXPECTED = {x['case']:x for x in FAMILY['cases']}
assert set(EXPECTED)==set(CASES)
OUT.mkdir(exist_ok=False)
state = {'scope':'Candidate search only; UNSAT requires a separate checked certificate.',
         'started':datetime.datetime.now(datetime.timezone.utc).isoformat(), 'cases':{}}
stopping = False
active = None

def stop(sig, frame):
    global stopping
    stopping = True

def save():
    p=OUT/'portfolio.json.tmp'
    p.write_text(json.dumps(state,indent=2)+'\n')
    p.replace(OUT/'portfolio.json')

def limits():
    resource.setrlimit(resource.RLIMIT_AS,(1500*1024**2,1500*1024**2))

signal.signal(signal.SIGTERM,stop)
signal.signal(signal.SIGINT,stop)
try:
    for name in CASES:
        if stopping or (ROOT/'DESK_ERROR.response').exists(): break
        subprocess.run(['python',str(ROOT/'renew.py')],check=True)
        cnf=CNFS/(name+'.cnf')
        meta=json.loads(cnf.with_suffix('.json').read_text())
        assert hashlib.sha256(cnf.read_bytes()).hexdigest()==meta['sha256']==EXPECTED[name]['cnf_sha256']
        assert hashlib.sha256(cnf.with_suffix('.json').read_bytes()).hexdigest()==EXPECTED[name]['metadata_sha256']
        command=[str(SOLVER),'--sat','--time=300',str(cnf)]
        started=time.monotonic()
        with (OUT/(name+'.stdout')).open('x') as stdout, (OUT/(name+'.stderr')).open('x') as stderr:
            active=subprocess.Popen(command,stdout=stdout,stderr=stderr,start_new_session=True,preexec_fn=limits)
            state['cases'][name]={'pid':active.pid,'command':command,'cnf_sha256':meta['sha256'],
                'started':datetime.datetime.now(datetime.timezone.utc).isoformat()}
            save(); print('START',name,active.pid,flush=True)
            while active.poll() is None:
                if stopping or (ROOT/'DESK_ERROR.response').exists() or time.monotonic()-started>330:
                    os.killpg(active.pid,signal.SIGINT)
                    try: active.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        os.killpg(active.pid,signal.SIGKILL);active.wait()
                    break
                time.sleep(1)
            code=active.wait(); active=None
        statuses=[s for s in (OUT/(name+'.stdout')).read_text().splitlines() if s.startswith('s ')]
        state['cases'][name].update(exit_code=code,status_lines=statuses,elapsed_seconds=time.monotonic()-started,
            finished=datetime.datetime.now(datetime.timezone.utc).isoformat())
        save();print('FINISH',name,code,statuses,flush=True)
        if code==10 or statuses==['s SATISFIABLE']:
            state['candidate_requires_validation']=name;save();break
        if code not in (0,20) and not stopping:
            state['unexpected_solver_exit']=code;save();break
finally:
    if active is not None and active.poll() is None:
        os.killpg(active.pid,signal.SIGTERM)
        try: active.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(active.pid,signal.SIGKILL);active.wait()
    save()
