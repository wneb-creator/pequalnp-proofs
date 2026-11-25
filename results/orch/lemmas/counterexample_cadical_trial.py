import sys
sys.dont_write_bytecode=True
import argparse,json,time,subprocess,re
from pathlib import Path
from counterexample_cnf import emit,z3
ap=argparse.ArgumentParser();ap.add_argument('--N',type=int,required=True);ap.add_argument('--mask',type=int,required=True);ap.add_argument('--gates',type=int,required=True);ap.add_argument('--clean',action='store_true');ap.add_argument('--timeout',type=int,default=90);ap.add_argument('--label',required=True);a=ap.parse_args()
assert re.fullmatch(r'[a-z0-9-]+',a.label)
base=Path('/tmp/oec/pequalnp-pilot-51');cnf=base/(a.label+'.cnf');stdout=base/(a.label+'-cadical.stdout');stderr=base/(a.label+'-cadical.stderr')
s,sels,goal,full_xs,target,forbidden=emit(a.N,a.mask,a.gates,a.clean,a.timeout,str(cnf))
started=time.monotonic()
with stdout.open('w') as out,stderr.open('w') as err:
    proc=subprocess.run([str(base/'lean-4.36.0-linux/bin/cadical'),'-t',str(a.timeout),str(cnf)],stdout=out,stderr=err)
result={'N':a.N,'mask':a.mask,'gates':a.gates,'clean':a.clean,'solver':'CaDiCaL2.1.2','exit_code':proc.returncode,'status':{10:'sat',20:'unsat',0:'unknown'}.get(proc.returncode,'error'),'elapsed_s':time.monotonic()-started,'stdout':str(stdout),'stderr':str(stderr)}
if proc.returncode==10:
    values={}
    for line in stdout.read_text().splitlines():
        if line.startswith('v '):
            for word in line.split()[1:]:
                number=int(word)
                if number:values[abs(number)]=number>0
    names={}
    for line in cnf.read_text().splitlines():
        if line.startswith('c '):
            _,number,name=line.split(' ',2);names[int(number)]=name
    atoms={};stack=list(goal)
    while stack:
        term=stack.pop()
        if z3.is_const(term) and z3.is_bool(term) and term.decl().kind()==z3.Z3_OP_UNINTERPRETED:atoms[str(term.decl().name())]=term
        else:stack.extend(term.children())
    raw_model=z3.Model()
    for number,truth in values.items():
        if number in names and names[number] in atoms:
            raw_model.update_value(atoms[names[number]],z3.BoolVal(truth))
    assert all(z3.is_true(raw_model.eval(clause,model_completion=True)) for clause in goal)
    model=goal.convert_model(raw_model)
    assert all(z3.is_true(model.eval(clause,model_completion=True)) for clause in s.assertions())
    wires=full_xs[:];gates=[]
    for aa,bb,op in sels:
        left=model.eval(aa,model_completion=True).as_long();right=model.eval(bb,model_completion=True).as_long();isand=z3.is_true(model.eval(op,model_completion=True))
        assert 0<=left<=right<len(wires)
        val=wires[left]&wires[right] if isand else wires[left]|wires[right]
        if a.clean and isand:assert not val&forbidden
        wires.append(val);gates.append(['and' if isand else 'or',left,right])
    assert wires[-1]==target
    result['verified_circuit']=gates
print(json.dumps(result),flush=True)
