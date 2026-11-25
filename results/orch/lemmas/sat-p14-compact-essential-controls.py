import copy,hashlib,importlib.util,json
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81');namespace={}
exec(compile((BASE/'sat-p14-compact-controls.py').read_text().split('reports=[]')[0],'compact-control-helpers','exec'),namespace)
spec=importlib.util.spec_from_file_location('essential',BASE/'sat-p14-compact-essential.py');essential=importlib.util.module_from_spec(spec);spec.loader.exec_module(essential);nine=essential.nine;quiet=essential.quiet

def assign_prefix(m,control):
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
 assert set(A)==set(range(1,m['incomparability']['variable_begin']+1))
 return A

reports=[]
for tag,control,cap,equality,negative_proxy,graph,nine_free,incomparable in [
 ('sat-p14-compact-essential28-control',namespace['flatten'](json.loads((BASE/'sat-fano-canonical28-control.json').read_text())['gates']),8,False,False,'fano',False,True),
 ('sat-p14-compact-essential-host-control',json.loads((BASE/'constructive-compact-host-control.json').read_text()),21,True,True,'matching',True,False)]:
 control=nine.canonicalize(control);control.update(graph=graph,equality=equality,negative_proxy=negative_proxy)
 c,m=essential.build(cap,equality,negative_proxy,graph,nine_free,incomparable);c.write(BASE/(tag+'.cnf'));(BASE/(tag+'.metadata.json')).write_text(json.dumps(m,indent=2)+'\n')
 A=assign_prefix(m,control)
 for atom,new in zip(m['atoms'],m['incomparability']['atoms']):
  left,right=atom['slots']
  for first,second,terms in [(left,right,new['directions'][0]),(right,left,new['directions'][1])]:
   for row,v in zip(m['incomparability']['negative_rows'],terms):
    assert v not in A;A[v]=A[first['values'][row]] and not A[second['values'][row]]
 assert set(A)==set(range(1,m['variables']+1))
 for i,clause in enumerate(c.cs):assert any(A[abs(v)] if v>0 else not A[-v] for v in clause),(tag,i,clause)
 quiet.core.validate(control);assert not quiet.compact_derivative(control,0,7) and not quiet.compact_derivative(control,7,0)
 (BASE/(tag+'.compact-control.json')).write_text(json.dumps(control,indent=2)+'\n');(BASE/(tag+'.complete-assignment.json')).write_text(json.dumps(A)+'\n')
 reports.append(dict(tag=tag,active_atoms=len(control['atoms']),cap=cap,variables=m['variables'],clauses=m['clauses'],truth_rows=16384,marked_derivatives=[False,False],incomparability=incomparable,equality=equality,nine_free=nine_free,scope='Exact28 Fano quiet control: new cut enabled, size27 equality/nine-free disabled' if graph=='fano' else 'Hosted matching, not Fano: old equality/nine-free enabled, new minimality cut disabled'))
report=dict(verdict='PASS',source_sha256=hashlib.sha256((BASE/'sat-p14-compact-essential.py').read_bytes()).hexdigest(),controls=reports,scope='Author complete controls; no solver launched and no target existence/refutation claim')
(BASE/'sat-p14-compact-essential-controls.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
