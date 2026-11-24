from pathlib import Path
import importlib.util,itertools,json,hashlib
B=Path('/tmp/oec/pequalnp-pilot-21/search')
spec=importlib.util.spec_from_file_location('five_allcost_test',B/'cegis-general-five-canonical-allcost.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
original=m.formal_cost.exact_costs;captured=[]
def capture(*args,**kwargs):
 rows=original(*args,**kwargs);captured[:]=rows;return rows
m.formal_cost.exact_costs=capture
c=m.f.b.CNF();m.encode(c,[]);rows=captured[-5:];units=c.cs[-5:]
assert units==[(row[5],) for row in rows]
accepted=[]
for choice in itertools.product(range(6),repeat=5):
 values={v:i==value for row,value in zip(rows,choice) for i,v in enumerate(row)}
 actual=all(any(values[abs(v)]==(v>0) for v in clause) for clause in units)
 assert actual==all(value==5 for value in choice)
 if actual:accepted.append(choice)
class Count(m.f.b.CNF):
 def __init__(self):self.n=0;self.count=0
 def add(self,*xs):self.count+=1
cc=Count();m.encode(cc,m.f.ROWS)
assert cc.n==129594 and cc.count==2680570
report={'status':'PASS','tested_output_cost_tuples':6**5,'accepted_tuples':accepted,'full_variables':cc.n,'full_clauses':cc.count,'solver_launched':False,'runner_sha256':hashlib.sha256((B/'cegis-general-five-canonical-allcost.py').read_bytes()).hexdigest()}
(B/'general-five-allcost-test.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
