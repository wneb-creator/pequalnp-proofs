import copy,hashlib,importlib.util,json
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81');namespace={}
exec(compile((BASE/'sat-p14-compact-controls.py').read_text().split('reports=[]')[0],'compact-control-helpers','exec'),namespace)
spec=importlib.util.spec_from_file_location('nine',BASE/'sat-p14-compact-nine.py');nine=importlib.util.module_from_spec(spec);spec.loader.exec_module(nine);quiet=nine.quiet
reports=[]
for tag,source in [('sat-p14-compact-nine35-control','sat-p14-compact35-control.compact-control.json'),('sat-p14-compact-nine-host-control','constructive-compact-host-control.json')]:
 m=json.loads((BASE/(tag+'.metadata.json')).read_text());control=nine.canonicalize(json.loads((BASE/source).read_text()));control.update(graph=m['graph'],equality=m['equality'],negative_proxy=m['negative_proxy'])
 original=copy.deepcopy(m);original['variables']=m['extension']['covers'][0]['terms'][0][0]-1;A=namespace['assign'](original,control)
 def put(v,b):
  assert v not in A;A[v]=bool(b)
 def dp(table):
  for cell in table['cells']:put(cell['var'],sum(A[v] for v in table['literals'][:cell['prefix']])>=cell['threshold'])
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
   put(row['left_term'],A[atom['slots'][0]['primary'][trace['base']]] and sd[1]);put(row['right_term'],sd[0] and A[atom['slots'][1]['primary'][trace['base']]])
   d=A[row['left_term']] or A[row['right_term']];put(row['out'],d);ds.append(d)
  for j,v in enumerate(trace['terms']):put(v,A[m['final'][j]] and ds[j])
  put(trace['out'],any(A[v] for v in trace['terms']));assert not A[trace['out']]
 assert set(A)==set(range(1,m['enhancements']['variable_begin']+1))
 for atom,flags in zip(m['atoms'],m['enhancements']['ordering']):
  for k,v in enumerate(flags):put(v,any(A[z] for s in atom['slots'] for z in s['prior'][k:]))
 for pair in m['enhancements']['cooccurrence']:
  x,y=pair['pair'];slots=[s for a in m['atoms'] for s in a['slots']]
  for slot,v in zip(slots,pair['terms']):put(v,A[slot['primary'][x]] and A[slot['primary'][y]])
  put(pair['out'],any(A[v] for v in pair['terms']))
 for center in m['enhancements']['centers']:dp(center['all_at_least_six']);dp(center['free_at_least_two'])
 assert set(A)==set(range(1,m['variables']+1));count=0
 with (BASE/(tag+'.cnf')).open() as f:
  assert f.readline().split()==['p','cnf',str(m['variables']),str(m['clauses'])]
  for line in f:
   clause=list(map(int,line.split()))[:-1];assert any(A[abs(v)] if v>0 else not A[-v] for v in clause),(tag,count,clause);count+=1
 assert count==m['clauses'];quiet.core.validate(control);assert not quiet.compact_derivative(control,0,7) and not quiet.compact_derivative(control,7,0)
 maxima=[max([k for s in a['slots'] for k in s['prior']],default=-1) for a in control['atoms']];assert maxima==sorted(maxima)
 (BASE/(tag+'.compact-control.json')).write_text(json.dumps(control,indent=2)+'\n');(BASE/(tag+'.complete-assignment.json')).write_text(json.dumps(A)+'\n')
 reports.append(dict(tag=tag,active_atoms=len(control['atoms']),variables=len(A),clauses=count,truth_rows=16384,marked_derivatives=[False,False],nine_free=m['enhancements']['nine_free'],maxima=maxima,scope='Generic35 Fano control; size27 equality/nine-free disabled' if not m['enhancements']['nine_free'] else 'Hosted matching control, not Fano; all structural/cut clauses satisfied'))
c=quiet.core.CNF();xs=[c.var() for _ in range(13)];six=c.threshold(xs,6);two=c.threshold(xs[:4],2);c.add(-six['root'],two['root']);accepted=rejected=0
for mask in range(1<<13):
 A={v:bool(mask>>i&1) for i,v in enumerate(xs)}
 for table in [six,two]:
  for cell in table['cells']:A[cell['var']]=sum(A[v] for v in table['literals'][:cell['prefix']])>=cell['threshold']
 actual=all(any(A[abs(v)] if v>0 else not A[-v] for v in clause) for clause in c.cs);expected=mask.bit_count()<6 or (mask&15).bit_count()>=2;assert actual==expected
 if actual:accepted+=1
 else:rejected+=1
report=dict(verdict='PASS',source_sha256=hashlib.sha256((BASE/'sat-p14-compact-nine.py').read_bytes()).hexdigest(),controls=reports,cut_truth_table=dict(rows=8192,accepted=accepted,rejected=rejected),scope='Author complete controls and exact cardinality-cut truth table; no solver result.')
(BASE/'sat-p14-compact-nine-controls.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
