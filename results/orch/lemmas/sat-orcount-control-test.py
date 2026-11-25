import sys,json,hashlib,collections,datetime
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-81')
sys.argv=['status-final-fano-sat-review.py',str(base)]
exec(compile((base/'status-final-fano-sat-review.py').read_text(),'status-final-fano-sat-review.py','exec'))
new=json.loads((base/'sat-fano-orcount28-control.metadata.json').read_text())
assert all(new[k]==minimal[k] for k in minimal if k not in ('variables','clauses'))
assert len(new['false_or_count'])==37
rows=[]
def add(v,b):
 assert isinstance(v,int) and not isinstance(v,bool) and v not in assignment and 10193<=v<=new['variables']
 assignment[v]=bool(b)
for r in new['false_or_count']:
 row=r['row'];mask=r['mask'];required=r['required']
 assert mask==new['tests'][row] and mask in new['negative']
 assert required==13-mask.bit_count()
 assert len(r['gate_literals'])==28
 q=[]
 for j,v in enumerate(r['gate_literals']):
  truth=gates[j][0]=='or' and not vals[14+j][row]
  add(v,truth);q.append(truth)
 assert sum(q)>=required
 dp=r['dp'];assert dp['literals']==r['gate_literals'] and dp['threshold']==required
 expected=[(i,j) for i in range(1,29) for j in range(1,min(i,required)+1)]
 assert [(c['prefix'],c['threshold']) for c in dp['cells']]==expected
 for cell in dp['cells']:add(cell['var'],sum(q[:cell['prefix']])>=cell['threshold'])
 assert assignment[dp['root']]
 rows.append(dict(mask=mask,required=required,count=sum(q),slack=sum(q)-required))
assert len(assignment)==new['variables']
count=0
with (base/'sat-fano-orcount28-control.cnf').open() as f:
 assert f.readline().split()==['p','cnf',str(new['variables']),str(new['clauses'])]
 for line in f:
  clause=list(map(int,line.split()));assert clause[-1]==0
  assert cnf_sat([clause[:-1]],assignment)
  count+=1
assert count==new['clauses']
report=dict(verdict='PASS',variables=len(assignment),clauses=count,rows=rows,threshold_census=dict(collections.Counter(x['required'] for x in rows)),source_sha256=hashlib.sha256((base/'sat-fano-orcount.py').read_bytes()).hexdigest())
(base/'sat-orcount-control-test.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='rows'}))
