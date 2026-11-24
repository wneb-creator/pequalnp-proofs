"""Bounded CaDiCaL compatibility controls using the unchanged pushed runner."""
from pathlib import Path
import hashlib
import itertools
import json
import subprocess
import sys
import time

ROOT=Path('/tmp/oec/pequalnp-pilot-18')
OUT=ROOT/'lean-setup/cadical-streaming-controls'
RUNNER=Path('/workspace/pequalnp-proofs/results/pilot-18/search/run_checked_kissat.py')
SOLVER=ROOT/'lean-4.36.0-linux/bin/cadical'
CHECKER=ROOT/'solver/dsr-trim/bin/dsr-trim'
RUNNER_SHA='535ff6e32a68a31eefa1545f031483d0e9b73acd79066d1bbb2a2f42c86685bb'
SOLVER_SHA='2a0137451efde370d67b88aec26f1e902870f095b1204b07049a103bc6bbd647'
CHECKER_SHA='e6894b5b74ac2c09b494344f397ec5111547aaa782cdb399f1a8b6835ecef84b'
sha=lambda b:hashlib.sha256(b).hexdigest()
for path,h in [(RUNNER,RUNNER_SHA),(SOLVER,SOLVER_SHA),(CHECKER,CHECKER_SHA)]:assert sha(path.read_bytes())==h


def write_cnf(name,n,clauses):
    p=OUT/(name+'.cnf')
    assert not p.exists()
    p.write_text(f'p cnf {n} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
    return p


def pigeonhole(pigeons,holes):
    v=lambda p,h:p*holes+h+1
    clauses=[[v(p,h) for h in range(holes)] for p in range(pigeons)]
    clauses += [[-v(p,h),-v(q,h)] for h in range(holes) for p,q in itertools.combinations(range(pigeons),2)]
    return pigeons*holes,clauses


def clique_coloring(vertices,colors):
    v=lambda p,c:p*colors+c+1
    clauses=[[v(p,c) for c in range(colors)] for p in range(vertices)]
    clauses += [[-v(p,c),-v(p,d)] for p in range(vertices) for c,d in itertools.combinations(range(colors),2)]
    clauses += [[-v(p,c),-v(q,c)] for p,q in itertools.combinations(range(vertices),2) for c in range(colors)]
    return vertices*colors,clauses


fixtures=[('small-sat',2,[[1,2],[-1,2]],'SAT_UNVALIDATED'),
          ('clique4-colors3',*clique_coloring(4,3),'VERIFIED_UNSAT'),
          ('pigeons7-holes6',*pigeonhole(7,6),'VERIFIED_UNSAT'),
          ('pigeons6-holes6',*pigeonhole(6,6),'SAT_UNVALIDATED')]
reports={}
for name,n,clauses,expected in fixtures:
    cnf=write_cnf(name,n,clauses)
    command=[sys.executable,str(RUNNER),str(cnf),str(OUT/name),'--solver',str(SOLVER),
             '--checker',str(CHECKER),'--checker-sha256',CHECKER_SHA,'--cnf-sha256',sha(cnf.read_bytes()),
             '--solver-arg=--unsat','--max-seconds','30','--solver-memory-mb','512',
             '--checker-memory-mb','512','--min-free-mb','64']
    start=time.monotonic()
    with (OUT/(name+'.runner.stdout.txt')).open('xb') as so,(OUT/(name+'.runner.stderr.txt')).open('xb') as se:
        process=subprocess.run(command,stdout=so,stderr=se,timeout=40)
    result=json.loads((OUT/name/'result.json').read_text())
    assert result['status']==expected,(name,result)
    assert result['solver_sha256']==SOLVER_SHA and result['checker_sha256']==CHECKER_SHA
    assert result['proof_stream_complete'] and result['checker_exit']==0
    assert not (OUT/name/'proof.fifo').exists()
    if expected=='VERIFIED_UNSAT':
        assert process.returncode==0 and result['solver_exit']==20
        assert result['solver_verdicts']==['s UNSATISFIABLE'] and result['checker_verdicts']==['s VERIFIED UNSAT']
        assert result['accepted_CNF_UNSAT'] and result['proof_bytes_read']>5
    else:
        assert process.returncode==10 and result['solver_exit']==10
        assert result['solver_verdicts']==['s SATISFIABLE'] and result['checker_verdicts']==['s VALID']
        assert result['accepted_CNF_UNSAT'] is False
        # Independent exhaustive/complete-model CNF check for these small SAT fixtures.
        signed=[]
        for line in (OUT/name/'solver.stdout.txt').read_text().splitlines():
            if line.startswith('v '):signed.extend(int(x) for x in line.split()[1:] if x!='0')
        assignment={}
        for lit in signed:
            assert 1<=abs(lit)<=n and (abs(lit) not in assignment or assignment[abs(lit)]==(lit>0))
            assignment[abs(lit)]=lit>0
        assert set(assignment)==set(range(1,n+1))
        assert all(any(assignment[abs(lit)]==(lit>0) for lit in c) for c in clauses)
    reports[name]={'runner_argv':command,'runner_exit':process.returncode,'wall_seconds':time.monotonic()-start,
                   'cnf_sha256':sha(cnf.read_bytes()),'variables':n,'clauses':len(clauses),
                   'runner_result':result,'result_sha256':sha((OUT/name/'result.json').read_bytes())}
    (OUT/'compatibility-controls.json').write_text(json.dumps(reports,indent=2)+'\n')
    print(json.dumps({'case':name,'status':result['status'],'solver_exit':result['solver_exit'],
                      'checker_verdicts':result['checker_verdicts'],'proof_bytes':result['proof_bytes_read'],
                      'seconds':result['elapsed_seconds']}),flush=True)

# Retain only a small nontrivial control proof for independent byte/hash checks.
name='clique4-colors3';proof=OUT/'clique4-colors3.direct.drat'
command=[str(SOLVER),'--unsat','--no-color',str(OUT/(name+'.cnf')),str(proof)]
with (OUT/'direct-proof-solver.stdout.txt').open('xb') as so,(OUT/'direct-proof-solver.stderr.txt').open('xb') as se:
    proc=subprocess.run(command,stdout=so,stderr=se,timeout=15)
assert proc.returncode==20
raw=proof.read_bytes();assert raw and raw[0] in (ord('a'),ord('d')) and b'\0' in raw
assert sha(raw)==reports[name]['runner_result']['proof_sha256']
assert len(raw)==reports[name]['runner_result']['proof_bytes_read']
checks={}
for label,data in [('valid',raw),('invalid-empty-claim',b'a\0')]:
    with (OUT/(label+'.checker.stdout.txt')).open('xb') as so,(OUT/(label+'.checker.stderr.txt')).open('xb') as se:
        proc=subprocess.run([str(CHECKER),'--forward',str(OUT/(name+'.cnf'))],input=data,stdout=so,stderr=se,timeout=15)
    statuses=[x for x in (OUT/(label+'.checker.stdout.txt')).read_text().splitlines() if x.startswith('s ')]
    if label=='valid':assert proc.returncode==0 and statuses==['s VERIFIED UNSAT']
    else:assert proc.returncode!=0 or statuses!=['s VERIFIED UNSAT']
    checks[label]={'exit':proc.returncode,'verdicts':statuses,'proof_sha256':sha(data),'proof_bytes':len(data)}

for path,h in [(RUNNER,RUNNER_SHA),(SOLVER,SOLVER_SHA),(CHECKER,CHECKER_SHA)]:assert sha(path.read_bytes())==h
summary={'verdict':'PASS_UNCHANGED_RUNNER_COMPATIBLE','runner_sha256':RUNNER_SHA,'solver_sha256':SOLVER_SHA,
         'checker_sha256':CHECKER_SHA,'solver_args':['--unsat'],'hardcoded_no_color_accepted':True,
         'controls':reports,'direct_control_proof':{'sha256':sha(raw),'bytes':len(raw),'matches_stream_hash':True},
         'direct_checker_positive_negative_controls':checks,'no_runner_or_checker_modification':True,
         'no_real_search_or_lease_actions':True}
(OUT/'compatibility-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'verdict':summary['verdict'],'control_count':len(reports)+1,
                  'control_proof_bytes':len(raw),'negative_control':checks['invalid-empty-claim']}))
