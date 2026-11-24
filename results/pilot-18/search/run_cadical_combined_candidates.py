"""Candidate-only diversification; UNKNOWN and uncertified UNSAT prove nothing."""
import datetime, hashlib, json, os, resource, signal, subprocess, time
from pathlib import Path

ROOT = Path('/tmp/oec/pequalnp-pilot-18')
CNFS = ROOT/'tail7-ancestor-support-antichain'
OUT = ROOT/'cadical-combined-candidates'
SOLVER = ROOT/'lean-4.36.0-linux/bin/cadical'
assert hashlib.sha256(SOLVER.read_bytes()).hexdigest()=='2a0137451efde370d67b88aec26f1e902870f095b1204b07049a103bc6bbd647'
CASES = ['meet5', 'meet3or2', 'meet2or1meet2']
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
        assert hashlib.sha256(cnf.read_bytes()).hexdigest()==meta['sha256']
        command=[str(SOLVER),'--sat','-t','600',str(cnf)]
        started=time.monotonic()
        with (OUT/(name+'.stdout')).open('x') as stdout, (OUT/(name+'.stderr')).open('x') as stderr:
            active=subprocess.Popen(command,stdout=stdout,stderr=stderr,start_new_session=True,preexec_fn=limits)
            state['cases'][name]={'pid':active.pid,'command':command,'cnf_sha256':meta['sha256'],
                'started':datetime.datetime.now(datetime.timezone.utc).isoformat()}
            save(); print('START',name,active.pid,flush=True)
            while active.poll() is None:
                if stopping or (ROOT/'DESK_ERROR.response').exists() or time.monotonic()-started>630:
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
