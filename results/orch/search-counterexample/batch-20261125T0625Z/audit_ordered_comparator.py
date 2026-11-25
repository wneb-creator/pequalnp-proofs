import ast,itertools,json,shutil,time
from pathlib import Path
import z3
base=Path('/tmp/oec/pequalnp-pilot-62');tree=ast.parse((base/'multi_output_direct_cnf.py').read_text());node=next(n for n in tree.body if isinstance(n,ast.ClassDef) and n.name=='CNF');scope={'Path':Path,'shutil':shutil};exec(compile(ast.Module(body=[node],type_ignores=[]),'CNF','exec'),scope)
cnf=scope['CNF'](base/'ordered-comparator-control.cnf');previous=[cnf.var() for _ in range(3)];branches=[[cnf.var() for _ in range(3)] for _ in range(2)];current=[cnf.disj([a,b]) for a,b in zip(*branches)]
depends=[cnf.conj(cnf.disj([cnf.neg(a),b]) for a,b in zip(sig,previous)) for sig in branches];equal=True;less=[]
for a,b in reversed(list(zip(previous,current))):
 less.append(cnf.conj([equal,cnf.neg(a),b]));equal=cnf.conj([equal,cnf.disj([cnf.neg(a),b]),cnf.disj([a,cnf.neg(b)])])
cnf.add(depends+less+[equal]);cnf.finish();variables={i:z3.Bool('v'+str(i)) for i in range(1,cnf.variables+1)};solver=z3.Solver()
for line in (base/'ordered-comparator-control.cnf').read_text().splitlines():
 if not line or line[0] in 'cp':continue
 lits=[int(x) for x in line.split()[:-1]];solver.add(z3.Or(*[variables[abs(x)] if x>0 else z3.Not(variables[-x]) for x in lits]))
start=time.monotonic();tested=0
for p,a,b in itertools.product(range(8),repeat=3):
 assumptions=[]
 for bits,value in [(previous,p),(branches[0],a),(branches[1],b)]:
  assumptions.extend(variables[x] if value>>i&1 else z3.Not(variables[x]) for i,x in enumerate(bits))
 expected=(a&p==a) or (b&p==b) or (p<=a|b)
 result=solver.check(*assumptions);assert (result==z3.sat)==expected,(p,a,b,result,expected);tested+=1
report={'tested':tested,'result':'passed','seconds':time.monotonic()-start,'variables':cnf.variables,'clauses':cnf.clauses,'scope':'Exhaustive3-bit unsigned comparator/dependency clause truth table'}
(base/'ordered-comparator-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(report)
