import ast
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import shutil
import z3

base=Path('/tmp/oec/pequalnp-pilot-62')
source=base/'multi_output_direct_cnf.py'
syntax=ast.parse(source.read_text())
node=next(x for x in syntax.body if isinstance(x,ast.ClassDef) and x.name=='CNF')
ns={'shutil':shutil}
exec(compile(ast.Module(body=[node],type_ignores=[]),str(source),'exec'),ns)
CNF=ns['CNF']
tmp=base/'direct-cnf-audit.cnf'
checks=0
def formula(c):
    c.finish()
    xs=[z3.Bool('x'+str(i)) for i in range(c.variables+1)]
    s=z3.Solver()
    for line in tmp.read_text().splitlines():
        if line.startswith('p '):continue
        lits=list(map(int,line.split()))[:-1]
        s.add(z3.Or([xs[x] if x>0 else z3.Not(xs[-x]) for x in lits]))
    return s,xs
def lit_value(lit,bits):
    if type(lit) is bool:return lit
    return bits[abs(lit)-1] if lit>0 else not bits[-lit-1]
def expr(lit,xs):
    if type(lit) is bool:return z3.BoolVal(lit)
    return xs[lit] if lit>0 else z3.Not(xs[-lit])
terms=[[],[True],[False],[1],[-1],[1,-1],[1,1,2],[True,-2,3],[False,1,2],[-1,2,-3]]
for kind in ('conj','disj'):
    for term in terms:
        c=CNF(tmp)
        for _ in range(3):c.var()
        out=getattr(c,kind)(term)
        s,xs=formula(c)
        for bits in product((False,True),repeat=3):
            expected=(all if kind=='conj' else any)(lit_value(lit,bits) for lit in term)
            s.push()
            s.add(*[xs[i+1]==b for i,b in enumerate(bits)])
            assert s.check()==z3.sat
            s.add(expr(out,xs)!=expected)
            assert s.check()==z3.unsat
            s.pop();checks+=1
for n in range(1,6):
    for k in range(n+2):
        for signed in (False,True):
            c=CNF(tmp)
            inputs=[c.var() for _ in range(n)]
            if signed:inputs=[-x if i%2 else x for i,x in enumerate(inputs)]
            c.at_least(inputs,k)
            s,xs=formula(c)
            for bits in product((False,True),repeat=n):
                expected=sum(lit_value(x,bits) for x in inputs)>=k
                s.push();s.add(*[xs[i+1]==b for i,b in enumerate(bits)])
                assert (s.check()==z3.sat)==expected
                s.pop();checks+=1
for left,right in product((True,False,1,-1,2,-2),repeat=2):
    c=CNF(tmp)
    c.var();c.var();c.equal(left,right)
    s,xs=formula(c)
    for bits in product((False,True),repeat=2):
        expected=lit_value(left,bits)==lit_value(right,bits)
        s.push();s.add(xs[1]==bits[0],xs[2]==bits[1])
        assert (s.check()==z3.sat)==expected
        s.pop();checks+=1
data=json.loads((base/'multi-output-line-neighborhoods.json').read_text())
witness_checks=[]
for name in ('direct-triangle-control9','direct-full-control39'):
    witness=json.loads((base/(name+'.witness.json')).read_text())
    vertices=witness['line_inputs']
    target_masks=[data['targets'][p]['positive_mask'] for p in witness['points']]
    count=0
    for q in range(1<<len(vertices)):
        global_q=sum(1<<v for i,v in enumerate(vertices) if q>>i&1)
        if any(global_q&t==t for t in data['allowed_concurrent_triples']):continue
        values=[bool(q>>i&1) for i in range(len(vertices))]
        for a,b in witness['operand_wire_lists']:
            assert a and b and all(0<=i<len(values) for i in a+b)
            values.append(all(values[i] for i in a) or all(values[i] for i in b))
        for target,indices in zip(target_masks,witness['output_wire_lists']):
            assert indices and all(0<=i<len(values) for i in indices)
            assert all(values[i] for i in indices)==bool(global_q&target)
        count+=1
    assert count==witness['checked_assignments']
    witness_checks.append({'name':name,'or_count':witness['or_count'],'inputs':len(vertices),'outputs':len(target_masks),'cap_assignments':count,'comparisons':count*len(target_masks)})
result={'source_sha256':sha256(source.read_bytes()).hexdigest(),'primitive_truth_checks':checks,'witness_checks':witness_checks,'status':'Independent primitive and witness checks passed.'}
print(json.dumps(result,indent=2))
(base/'direct-cnf-audit.json').write_text(json.dumps(result,indent=2)+'\n')
