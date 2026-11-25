import importlib.util
import itertools
import json
from pathlib import Path
import subprocess
import time

base=Path('/tmp/oec/pequalnp-pilot-96')
spec=importlib.util.spec_from_file_location('pilot_sat',base/'counterexample_sat.py')
sat=importlib.util.module_from_spec(spec)
spec.loader.exec_module(sat)
out=base/'sat-exact-four-not'
out.mkdir(exist_ok=True)
solver=str(base/'toolchain/lean-4.36.0-linux/bin/cadical')
limit=900

# Independently verify the cardinality construction for all small assignments.
for n in range(1,9):
    for wanted in range(n+1):
        pos=[tuple(c) for c in itertools.combinations(range(n),wanted+1)]
        neg=[tuple(c) for c in itertools.combinations(range(n),n-wanted+1)]
        for bits in itertools.product([False,True],repeat=n):
            allowed=all(not all(bits[i] for i in c) for c in pos) and all(any(bits[i] for i in c) for c in neg)
            assert allowed==(sum(bits)==wanted)
print('Cardinality construction checked exhaustively for n=1..8 and every target count.',flush=True)

rows=sorted({s for s in range(1024) if not sat.target(s)} | {(1<<a)|(1<<b) for a,b in sat.EDGES})
begin=time.monotonic()
for iteration in range(20):
    cnf,choices=sat.encode(rows,19,'any',False)
    nots=[n for _,_,n,_ in choices]
    for subset in itertools.combinations(nots,5):cnf.add(*[-n for n in subset])
    for subset in itertools.combinations(nots,16):cnf.add(*subset)
    # The OR choice is semantically ignored at a NOT, so choose its false representative.
    for _,_,n,o in choices:cnf.add(-n,-o)
    stem=out/f'iteration-{iteration:02d}'
    cnf.write(stem.with_suffix('.cnf'))
    seconds=max(1,limit-int(time.monotonic()-begin))
    print('ITERATION',iteration,'rows',len(rows),'vars',cnf.variables,'clauses',len(cnf.clauses),'remaining',seconds,flush=True)
    with stem.with_suffix('.stdout').open('w') as stdout,stem.with_suffix('.stderr').open('w') as stderr:
        proc=subprocess.run([solver,'-q','-t',str(seconds),'--seed=42592096',str(stem.with_suffix('.cnf'))],stdout=stdout,stderr=stderr)
    print('SOLVER_EXIT',proc.returncode,'elapsed',round(time.monotonic()-begin,2),flush=True)
    if proc.returncode==20:
        print('UNSAT for exact-four-NOT encoded final-output class; no general or Lean-checked lower-bound claim.',flush=True)
        break
    if proc.returncode!=10:break
    text=stem.with_suffix('.stdout').read_text()
    truth={int(v) for line in text.splitlines() if line.startswith('v ') for v in line[2:].split() if int(v)>0}
    assert sum(n in truth for n in nots)==4
    # Check every solver model clause independently before decoding.
    assert all(any((v in truth) if v>0 else (-v not in truth) for v in clause) for clause in cnf.clauses)
    gates=sat.decode(truth,choices)
    wrong=sat.check(gates)
    stem.with_suffix('.json').write_text(json.dumps({'gates':gates,'mismatches':wrong},indent=2)+'\n')
    print('MISMATCHES',len(wrong),flush=True)
    if not wrong:
        (out/'witness.json').write_text(json.dumps({'gates':gates,'not_count':4,'false_wire':10,'actual_false_wire':29,'output':28},indent=2)+'\n')
        print('WITNESS',flush=True)
        break
    rows=sorted(set(rows)|set(wrong))
    if time.monotonic()-begin>=limit:break
