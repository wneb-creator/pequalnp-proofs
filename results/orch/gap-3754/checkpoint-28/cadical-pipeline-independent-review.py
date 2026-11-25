from pathlib import Path
from itertools import product
import sys,json,hashlib
sys.path.insert(0, '/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
base=Path(__file__).parent
meta=json.loads((base/'cadical-matching4-control.metadata.json').read_text())
modeldata=json.loads((base/'cadical-matching4-control.model.json').read_text())
smt=base/meta['smt_file']; cnf=base/'cadical-matching4-control.cnf'
assert hashlib.sha256(smt.read_bytes()).hexdigest()==meta['smt_sha256']
assert hashlib.sha256(cnf.read_bytes()).hexdigest()==meta['cnf_sha256']
assignment={}
for line in (base/'cadical-matching4-control.cadical.stdout').read_text().splitlines():
    if line.startswith('v '):
        for integer in map(int,line.split()[1:]):
            if integer:
                variable=abs(integer); truth=integer>0
                assert variable not in assignment or assignment[variable]==truth
                assignment[variable]=truth
clauses=[]; names={}; header=None
for line in cnf.read_text().splitlines():
    if line.startswith('p cnf '): header=tuple(map(int,line.split()[2:]))
    elif line.startswith('c '):
        _,number,name=line.split(maxsplit=2); names[int(number)]=name
    elif line.strip():
        clause=list(map(int,line.split())); assert clause[-1]==0; clauses.append(clause[:-1])
assert header==(meta['cnf_variables'],meta['cnf_clauses'])
assert len(clauses)==header[1]
assert set(assignment)==set(range(1,header[0]+1))
assert all(any(assignment[abs(literal)]==(literal>0) for literal in clause) for clause in clauses)
assert len(names)==header[0]
print('Independent DIMACS verification:',len(clauses),'clauses;',len(assignment),'assigned variables')
original=list(z3.parse_smt2_file(str(smt)))
goal=z3.Goal(models=True);goal.add(*original)
transformed=z3.Then('simplify','bit-blast','tseitin-cnf')(goal)
assert len(transformed)==1
converted_goal=transformed[0]
assert hashlib.sha256(converted_goal.dimacs().encode()).hexdigest()==meta['cnf_sha256']
atoms={}
pending=list(converted_goal)
while pending:
    expression=pending.pop()
    if z3.is_const(expression) and z3.is_bool(expression):
        name=str(expression.decl().name())
        assert name not in atoms or z3.eq(atoms[name],expression)
        atoms[name]=expression
    else:pending.extend(expression.children())
assert set(atoms)==set(names.values())
booleans=z3.Model()
for number,name in names.items(): booleans.update_value(atoms[name], z3.BoolVal(assignment[number]))
converted=converted_goal.convert_model(booleans)
assert all(z3.is_true(converted.eval(assertion,model_completion=True)) for assertion in original)
n=modeldata['n'];gates=modeldata['gates'];m=len(gates);q=modeldata['clean_ands'];L=m-2*q+1;iw=(n+m).bit_length()
reconstructed=[]
for i in range(L):
    operation='or' if z3.is_true(converted.eval(z3.Bool('or'+str(i)),model_completion=True)) else 'and'
    operands=[converted.eval(z3.BitVec(c+str(i),iw),model_completion=True).as_long() for c in ['a','b']]
    reconstructed.append([operation,*operands])
for i in range(q):
    reconstructed.append(['and',*[converted.eval(z3.BitVec(c+str(i),iw),model_completion=True).as_long() for c in ['ta','tb']]])
output=n+L
for i in range(1,q):
    reconstructed.append(['or',*sorted([output,n+L+i])]);output=n+len(reconstructed)-1
assert reconstructed==gates and output==modeldata['output']
print('Independent model conversion:',len(original),'original SMT assertions satisfied; circuit matches emitted JSON')
edges=[tuple(edge) for edge in modeldata['edges']]
def target(x): return any(x[a] and x[b] for a,b in edges)
def run(x, fault=None, replace=None):
    wires=list(x)
    for index,(op,a,b) in enumerate(gates):
        assert op in ['and','or'] and 0<=a<len(wires) and 0<=b<len(wires)
        if index==fault: value=False if replace is None else wires[replace]
        elif op=='and': value=wires[a] and wires[b]
        else: value=wires[a] or wires[b]
        wires.append(value)
    return wires
inputs=list(product([False,True],repeat=n))
rows=[run(x) for x in inputs]
assert all(row[output]==target(x) for x,row in zip(inputs,rows))
below=[all(not row[w] or target(x) for x,row in zip(inputs,rows)) for w in range(n+m)]
dirty=[i for i,(op,a,b) in enumerate(gates) if op=='and' and not below[n+i]]
assert dirty==modeldata['dirty_and_indices'] and below[n:]==modeldata['below_gate']
cone=set()
def visit(w):
    if w<n or w in cone:return
    cone.add(w)
    _,a,b=gates[w-n];visit(a);visit(b)
visit(output)
assert cone==set(range(n,n+m))
for w in cone:
    op,a,b=gates[w-n]
    if op=='or' and not below[w]:
        for operand in [a,b]:
            implicant=below[operand] and any(row[operand] for row in rows)
            assert not implicant
for fault,(_,a,b) in enumerate(gates):
    for replacement in [None,a,b]:
        assert any(run(x,fault,replacement)[output]!=target(x) for x in inputs)
    edge_inputs=[tuple(i in edge for i in range(n)) for edge in edges]
    assert any(not run(x,fault,None)[output] for x in edge_inputs)
colors=modeldata['bipartition']
assert all(colors[a]!=colors[b] for a,b in edges)
for a in range(n):
    for b in range(a):
        assert sum(any(set(edge)=={a,k} for edge in edges) and any(set(edge)=={b,k} for edge in edges) for k in range(n))<=1
print('Independent scalar verification:',len(inputs),'assignments; valid AO2; exact graph output; all gates live and edge-critical; lift fixed; dirty AND gates',dirty)
print('All zero cuts and both parent bypasses change the output function.')
print('This seven-gate matching control is not least: its two-edge graph has a three-gate clean implementation.')
