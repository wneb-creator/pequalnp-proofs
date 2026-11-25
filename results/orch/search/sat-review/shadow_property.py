import ast
import itertools
import json
from pathlib import Path
from types import SimpleNamespace

path=Path('/tmp/oec/pequalnp-pilot-70/circuit-search/synthesize.py')
tree=ast.parse(path.read_text())
functions=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name in {'var','clause','mux_vector'}]
main_loop=next(x for x in tree.body if isinstance(x,ast.For) and isinstance(x.target,ast.Name) and x.target.id=='i')
shadow=next(x for x in main_loop.body if isinstance(x,ast.If) and isinstance(x.test,ast.Attribute) and x.test.attr=='shadow_missing')
ns={'nv':0,'clauses':[],'args':SimpleNamespace(shadow_missing=3),'ninputs':2,'edges':[(0,1)]}
exec(compile(ast.Module(body=functions,type_ignores=[]),'actual-encoder-functions','exec'),ns)
v=ns['var'];truth=v();op=v();lin=[[v(),v()],[v(),v()]];quad=[[v()],[v()]]
ns.update({'truth':truth,'op':op,'linear':lin,'quadratic':quad,'left':[truth,-truth],'right':[-truth,truth]})
ns['clause'](truth)
exec(compile(ast.Module(body=[shadow],type_ignores=[]),'actual-shadow-block','exec'),ns)
source_ids=[op]+lin[0]+lin[1]+quad[0]+quad[1]
out_ids=ns['lo']+ns['qo']
checks=0
for bits in itertools.product([False,True],repeat=len(source_ids)):
 assignment={truth:True}|dict(zip(source_ids,bits))
 for ids,source in [(ns['la'],lin[0]),(ns['lb'],lin[1]),(ns['qa'],quad[0]),(ns['qb'],quad[1])]:
  assignment.update({i:assignment[s] for i,s in zip(ids,source)})
 is_or=assignment[op]
 expected=[is_or and (assignment[lin[0][i]] or assignment[lin[1][i]]) for i in range(2)]
 expected.append((assignment[quad[0][0]] or assignment[quad[1][0]]) if is_or else ((assignment[lin[0][0]] and assignment[lin[1][1]]) or (assignment[lin[0][1]] and assignment[lin[1][0]])))
 for outs in itertools.product([False,True],repeat=len(out_ids)):
  a=assignment|dict(zip(out_ids,outs))
  actual=all(any(a[abs(lit)]==(lit>0) for lit in c) for c in ns['clauses'])
  assert actual==(tuple(expected)==outs),(bits,outs,expected)
  checks+=1
cardinality_checks=0
for n in range(1,8):
 for k in range(1,min(n,3)+1):
  for bits in itertools.product([False,True],repeat=n):
   clauses_hold=all(any(bits[i] for i in range(n) if i not in omitted) for omitted in itertools.combinations(range(n),k-1))
   assert clauses_hold==(sum(bits)>=k),(n,k,bits)
   cardinality_checks+=1
print(json.dumps({'actual_shadow_cnf_assignments_checked':checks,'cardinality_assignments_checked':cardinality_checks,'status':'passed'},indent=2))
