import importlib.util
import itertools
import json
from pathlib import Path
import random
import subprocess

base=Path('/tmp/oec/pequalnp-pilot-96')
spec=importlib.util.spec_from_file_location('pilot_sat',base/'counterexample_sat.py')
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

def value(clause, assignment):
    return any(assignment[abs(v)] == (v > 0) for v in clause)

def audit_gate_models():
    rng=random.Random(1962592)
    checked=0
    for trial in range(30):
        gates=[]
        for j in range(5):
            op=rng.randrange(3)
            a=rng.randrange(11+j)
            b=0 if op==2 else rng.randrange(11+j)
            if op!=2:a,b=sorted([a,b])
            gates.append((op,a,b))
        if not any(g[0]==2 for g in gates):gates[0]=(2,0,0)
        rows=list(range(32)) + [rng.randrange(1024) for _ in range(16)]
        cnf,choices=mod.encode(rows,5,'any')
        assigned={}
        for (a,b,n,o),(op,ai,bi) in zip(choices,gates):
            assigned.update({v:i==ai for i,v in enumerate(a)})
            assigned.update({v:i==bi for i,v in enumerate(b)})
            assigned[n]=op==2
            assigned[o]=op==1
        index=max(assigned)+1
        output_units=set()
        for row in rows:
            wires=[bool(row & (1<<j)) for j in range(10)]+[False]
            for op,a,b in gates:
                av,bv=wires[a],wires[b]
                z=(not av) if op==2 else (av or bv) if op==1 else (av and bv)
                assigned[index]=av;assigned[index+1]=bv;assigned[index+2]=z
                index+=3;wires.append(z)
            output_units.add(index-1)
        assert max(assigned)==cnf.variables
        for clause in cnf.clauses:
            if len(clause)==1 and abs(clause[0]) in output_units:
                continue
            assert value(clause,assigned),(trial,clause,gates)
            checked+=1
    return checked

def tiny_controls():
    solver=str(base/'toolchain/lean-4.36.0-linux/bin/cadical')
    cases=[
        ('not_input',1,lambda s:not bool(s&1),10),
        ('one_gate_and_with_not',1,lambda s:bool(s&1) and bool(s&2),20),
        ('two_gate_and_with_dead_not',2,lambda s:bool(s&1) and bool(s&2),10),
        ('one_gate_true',1,lambda s:True,10),
        ('one_gate_false_with_not',1,lambda s:False,20),
        ('two_gate_false_with_not',2,lambda s:False,10),
    ]
    old=mod.target
    answers=[]
    try:
        for name,k,target,expected in cases:
            mod.target=target
            # All ten inputs independently range, so unused inputs cannot fake a constant.
            cnf,_=mod.encode(list(range(1024)),k,'any')
            path=base/('audit-'+name+'.cnf');cnf.write(path)
            with path.with_suffix('.stdout').open('w') as out,path.with_suffix('.stderr').open('w') as err:
                done=subprocess.run([solver,'-q','-t','10',str(path)],stdout=out,stderr=err)
            assert done.returncode==expected,(name,done.returncode,expected)
            answers.append({'name':name,'exit':done.returncode})
    finally:mod.target=old
    return answers

def control_model():
    cnf=base/'sat-control.cnf'
    output=(base/'sat-control.stdout').read_text()
    truth={int(v) for s in output.splitlines() if s.startswith('v ') for v in s[2:].split() if int(v)>0}
    clauses=0
    for line in cnf.read_text().splitlines():
        if line.startswith(('c','p')):continue
        clause=list(map(int,line.split()))[:-1]
        assert any((v in truth) if v>0 else (-v not in truth) for v in clause)
        clauses+=1
    return clauses

result={'random_forward_semantics_clauses':audit_gate_models(),
        'small_sat_controls':tiny_controls(),
        'pinned_control_model_clauses':control_model()}
(base/'sat-independent-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
