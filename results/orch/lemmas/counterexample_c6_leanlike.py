import sys
sys.dont_write_bytecode=True
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-51/z3-python')
import z3,json,subprocess,time,hashlib
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-51')
ws=[z3.BitVecVal(x,17) for x in [8745,17482,34956,65776,69376,126976,0,131071]]
s=z3.SolverFor('QF_BV')
def pick(v,values):
    r=z3.BitVecVal(0,17)
    for i in range(len(values)-1,-1,-1):r=z3.If(v==i,values[i],r)
    return r
for j in range(7):
    a=z3.BitVec('a'+str(j),4);b=z3.BitVec('b'+str(j),4);op=z3.Bool('and'+str(j));v=z3.BitVec('w'+str(j),17)
    s.add(z3.ULE(a,b),z3.ULT(b,len(ws)))
    va=pick(a,ws);vb=pick(b,ws)
    s.add(v==z3.If(op,va&vb,va|vb));ws.append(v)
s.add(ws[-1]==51808)
g=z3.Goal();g.add(*s.assertions());r=z3.Then('simplify','solve-eqs','bit-blast','tseitin-cnf')(g);assert len(r)==1
text=r[0].dimacs();cnf=base/'c6-leanlike.cnf';cnf.write_text(text)
print(json.dumps({'rows':17,'gates':7,'free_constants':True,'constraints':['earlier selectors','a<=b'],'cnf_header':next(x for x in text.splitlines() if x.startswith('p ')),'cnf_sha256':hashlib.sha256(text.encode()).hexdigest()}),flush=True)
started=time.monotonic()
with (base/'c6-leanlike-cadical.stdout').open('w') as out,(base/'c6-leanlike-cadical.stderr').open('w') as err:
    completed=subprocess.run([str(base/'lean-4.36.0-linux/bin/cadical'),'-t','120',str(cnf)],stdout=out,stderr=err)
print(json.dumps({'exit_code':completed.returncode,'status':{10:'sat',20:'unsat',0:'unknown'}.get(completed.returncode,'error'),'elapsed_s':time.monotonic()-started}),flush=True)
