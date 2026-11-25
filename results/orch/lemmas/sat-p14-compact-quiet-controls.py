import copy,hashlib,importlib.util,json
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
namespace={}
exec(compile((BASE/'sat-p14-compact-controls.py').read_text().split('reports=[]')[0],'compact-control-helpers','exec'),namespace)
spec=importlib.util.spec_from_file_location('quiet',BASE/'sat-p14-compact-quiet.py');quiet=importlib.util.module_from_spec(spec);spec.loader.exec_module(quiet)
reports=[]
for tag,source in [('sat-p14-compact-quiet35-control','sat-p14-compact35-control.compact-control.json'),('sat-p14-compact-quiet-host-control','constructive-compact-host-control.json')]:
 m=json.loads((BASE/(tag+'.metadata.json')).read_text());control=json.loads((BASE/source).read_text())
 for atom in control['atoms']:
  atom['slots'].sort(key=lambda s:min(s['primary']+[14+j for j in s['prior']]))
 control.update(graph=m['graph'],equality=m['equality'],negative_proxy=m['negative_proxy'])
 original=copy.deepcopy(m);original['variables']=m['extension']['covers'][0]['terms'][0][0]-1
 A=namespace['assign'](original,control)
 def put(v,b):
  assert v not in A;A[v]=bool(b)
 for cover in m['extension']['covers']:
  p,l=cover['edge']
  for atom,(q,r) in zip(m['atoms'],cover['terms']):
   s,t=atom['slots'];put(q,A[s['primary'][p]] and A[t['primary'][l]]);put(r,A[s['primary'][l]] and A[t['primary'][p]])
 for trace in m['extension']['traces']:
  ds=[]
  for atom,row in zip(m['atoms'],trace['atoms']):
   sd=[]
   for slot,slotrow in zip(atom['slots'],row['slots']):
    for k,v in enumerate(slotrow['terms']):put(v,A[slot['prior'][k]] and ds[k])
    d=A[slot['primary'][trace['seed']]] or any(A[v] for v in slotrow['terms']);put(slotrow['out'],d);sd.append(d)
   put(row['left_term'],A[atom['slots'][0]['primary'][trace['base']]] and sd[1])
   put(row['right_term'],sd[0] and A[atom['slots'][1]['primary'][trace['base']]])
   d=A[row['left_term']] or A[row['right_term']];put(row['out'],d);ds.append(d)
  for j,v in enumerate(trace['terms']):put(v,A[m['final'][j]] and ds[j])
  put(trace['out'],any(A[v] for v in trace['terms']))
  assert A[trace['out']]==quiet.compact_derivative(control,trace['base'],trace['seed'])==False
 assert set(A)==set(range(1,m['variables']+1))
 count=0
 with (BASE/(tag+'.cnf')).open() as f:
  assert f.readline().split()==['p','cnf',str(m['variables']),str(m['clauses'])]
  for line in f:
   clause=list(map(int,line.split()))[:-1]
   assert any(A[abs(v)] if v>0 else not A[-v] for v in clause),(tag,count,clause)
   count+=1
 assert count==m['clauses'];quiet.core.validate(control)
 (BASE/(tag+'.compact-control.json')).write_text(json.dumps(control,indent=2)+'\n')
 (BASE/(tag+'.complete-assignment.json')).write_text(json.dumps(A)+'\n')
 reports.append(dict(tag=tag,active_atoms=len(control['atoms']),variables=len(A),clauses=count,truth_rows=16384,marked_derivatives=[False,False],equality=m['equality'],negative_proxy=m['negative_proxy']))
report=dict(verdict='PASS',source_sha256=hashlib.sha256((BASE/'sat-p14-compact-quiet.py').read_bytes()).hexdigest(),controls=reports)
(BASE/'sat-p14-compact-quiet-controls.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
