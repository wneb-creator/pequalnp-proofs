import importlib.util
import itertools
import json
from pathlib import Path
import subprocess

base=Path('/tmp/oec/pequalnp-pilot-96')
spec=importlib.util.spec_from_file_location('repair',base/'repair_sat.py')
r=importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)
cardinality_cases=0
for n in range(1,7):
    for limit in range(n+1):
        subsets=list(itertools.combinations(range(n),limit+1))
        for equal in itertools.product([False,True],repeat=n):
            feasible=False
            for marked in itertools.product([False,True],repeat=n):
                if any(marked[i] and not equal[i] for i in range(n)):continue
                if all(any(marked[i] for i in subset) for subset in subsets):
                    feasible=True
                    break
            assert feasible==(n-sum(equal)<=limit)
            cardinality_cases+=1
baseline=r.load_baseline(base/'counterexample-best.txt')
wrong=r.sat.check(baseline)
assert len(wrong)==6
independent_wrong=[]
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
for mask in range(1024):
    wires=[bool(mask&(1<<i)) for i in range(10)]+[False]
    for op,a,b in baseline:
        wires.append((wires[a] and wires[b]) if op==0 else (wires[a] or wires[b]))
    expected=any(mask&(1<<a) and mask&(1<<b) for a,b in edges)
    if wires[-1]!=expected:independent_wrong.append(mask)
assert wrong==independent_wrong
controls=[]
for changed,limit,expected in [(1,0,20),(1,1,10),(4,4,10),(5,4,20),(19,19,10),(0,4,20)]:
    cnf,choices=r.sat.encode([],19,'any',False)
    r.add_neighborhood(cnf,choices,baseline,limit)
    for j,((a,b,n,o),(op,left,right)) in enumerate(zip(choices,baseline)):
        modified=j<changed
        cnf.add(a[left])
        cnf.add(b[0 if modified else right])
        cnf.add(n if modified else -n)
        cnf.add(-o if modified or op==0 else o)
    stem=base/f'repair-control-{changed}-{limit}'
    cnf.write(stem.with_suffix('.cnf'))
    with stem.with_suffix('.stdout').open('w') as stdout,stem.with_suffix('.stderr').open('w') as stderr:
        proc=subprocess.run([str(base/'toolchain/lean-4.36.0-linux/bin/cadical'),'-q','-t','5',str(stem.with_suffix('.cnf'))],stdout=stdout,stderr=stderr)
    assert proc.returncode==expected,(changed,limit,proc.returncode)
    if expected==10:
        truth={int(v) for line in stem.with_suffix('.stdout').read_text().splitlines() if line.startswith('v ') for v in line[2:].split() if int(v)>0}
        assert all(any(v in truth if v>0 else -v not in truth for v in clause) for clause in cnf.clauses)
        decoded=r.sat.decode(truth,choices)
        actual=sum(g!=h for g,h in zip(decoded,baseline))
        assert actual==changed and actual<=limit
    controls.append({'changed_gates':changed,'max_changes':limit,'expected':expected,'actual':proc.returncode})
report={'status':'PASS','cardinality_cases':cardinality_cases,'baseline_rows':1024,'baseline_mismatches':wrong,'controls':controls,'scope':'Neighborhood cardinality and baseline decoding; only a fixed-order Hamming neighborhood, not exhaustive synthesis.'}
(base/'repair-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
