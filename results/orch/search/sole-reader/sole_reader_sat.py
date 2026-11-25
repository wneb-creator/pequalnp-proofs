from pathlib import Path
from datetime import datetime, timezone
from itertools import combinations
import hashlib
import json
import subprocess
import sys

scratch=Path('/tmp/oec/pequalnp-pilot-93')
archive=Path('/workspace/pequalnp-proofs/results/orch/search/sole-reader')
cadical=scratch/'elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
mode=sys.argv[1]
seconds=int(sys.argv[2])
assert mode in ('one','two_edge','two_nonedge')
not_count=1 if mode=='one' else 2
second=None if mode=='one' else 1 if mode=='two_edge' else 2
archive.mkdir(parents=True,exist_ok=True)
prefix='sole_'+mode
base=scratch/'petersen19-full.cnf'
with base.open() as f:
    header=f.readline().split()
assert header[:2]==['p','cnf']
nv,nc=map(int,header[2:])
ix=lambda kind,j,a:(kind*20+j)*1055+a+1
clauses=[]
not_vars=[ix(0,j,3) for j in range(19)]
if not_count==1:
    clauses.append(not_vars)
    clauses.extend([[-a,-b] for a,b in combinations(not_vars,2)])
else:
    clauses.extend([[v for k,v in enumerate(not_vars) if k!=j] for j in range(19)])
    clauses.extend([[-a,-b,-c] for a,b,c in combinations(not_vars,3)])

uses={}
for raw in ([0] if second is None else [0,second]):
    us=[]
    for j in range(19):
        nv+=1
        u=nv
        us.append(u)
        a,b=ix(1,j,raw),ix(2,j,raw)
        clauses.extend([[-a,u],[-b,u],[-u,a,b]])
    clauses.append(us)
    clauses.extend([[-a,-b] for a,b in combinations(us,2)])
    uses[raw]=us
for j in range(19):
    clauses.append([-uses[0][j],-not_vars[j]])
    if second is not None:
        clauses.append([-uses[0][j],-uses[second][j]])

cnf=scratch/(prefix+'.cnf')
with base.open() as f,cnf.open('w') as out:
    f.readline()
    out.write(f'p cnf {nv} {nc+len(clauses)}\n')
    for line in f:
        out.write(line)
    for clause in clauses:
        out.write(' '.join(map(str,clause))+' 0\n')
manifest={'mode':mode,'not_count':not_count,'sole_inputs':list(uses),'input0_reader_binary':True,'readers_distinct':second is not None,'auxiliary_usage_variables':uses,'extra_clauses':clauses,'base_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'solver_time_limit_seconds':seconds,'started_at':datetime.now(timezone.utc).isoformat(),'scope':'Restricted SAT experiment. Completeness of normalization and the additional restrictions has not been formalized in Lean.'}
(archive/(prefix+'.manifest.json')).write_text(json.dumps(manifest,indent=2)+'\n')
stdout=archive/(prefix+'.stdout')
stderr=archive/(prefix+'.stderr')
print('START',mode,manifest['started_at'],'extra clauses',len(clauses),flush=True)
with stdout.open('w') as out,stderr.open('w') as err:
    process=subprocess.run([str(cadical),'-t',str(seconds),str(cnf)],stdout=out,stderr=err)
result={'mode':mode,'returncode':process.returncode,'completed_at':datetime.now(timezone.utc).isoformat(),'status':'SAT' if process.returncode==10 else 'UNSAT' if process.returncode==20 else 'UNKNOWN','is_counterexample':False,'scope':'SAT solver result only; UNSAT is not a Lean-checked lower bound.'}
if process.returncode==10:
    positive=set()
    for line in stdout.read_text().splitlines():
        if line.startswith('v '):
            positive.update(int(v) for v in line[2:].split() if int(v)>0)
    gates=[]
    selected=[]
    for j in range(19):
        ops=[op for op in (3,0,1,2) if ix(0,j,op) in positive]
        aa=[k for k in range(10+j+1) if ix(1,j,k) in positive]
        bb=[k for k in range(10+j+1) if ix(2,j,k) in positive]
        assert ops and aa and bb
        op=ops[0]
        a,b=aa[0],bb[0]
        gates.append({'op':'not','inputs':[a]} if op==3 else {'op':'and','inputs':[]} if op==2 else {'op':'and' if op==0 else 'or','inputs':[a,b]})
        selected.append({'op':op,'source1':a,'source2':b})
    outputs=[k for k in range(30) if ix(6,0,k) in positive]
    assert outputs
    output=outputs[0]
    errors=[]
    for row in range(1024):
        wires=[bool(row>>k&1) for k in range(10)]
        for gate in gates:
            vals=[wires[k] if k<len(wires) else False for k in gate['inputs']]
            value=not vals[0] if gate['op']=='not' else all(vals) if gate['op']=='and' else any(vals)
            wires.append(value)
        actual=wires[output] if output<len(wires) else False
        expected=bool(any(row>>a&row>>b&1 for a,b in edges))
        if actual!=expected:
            errors.append({'row':row,'actual':actual,'expected':expected})
    actual_not_count=sum(g['op']=='not' for g in gates)
    readers={raw:[j for j,g in enumerate(gates) if raw in g['inputs']] for raw in uses}
    assert actual_not_count==not_count
    assert all(len(js)==1 for js in readers.values())
    assert gates[readers[0][0]]['op']!='not'
    if second is not None:
        assert readers[0][0]!=readers[second][0]
    result.update({'gates':gates,'output':output,'rows_checked':1024,'errors':errors,'actual_not_count':actual_not_count,'sole_reader_gate_indices':readers,'is_counterexample':not errors,'selected_encoding_gates':selected})
    if not errors:
        print('COUNTEREXAMPLE',mode,flush=True)
(archive/(prefix+'.result.json')).write_text(json.dumps(result,indent=2)+'\n')
print('RESULT',json.dumps(result),flush=True)
