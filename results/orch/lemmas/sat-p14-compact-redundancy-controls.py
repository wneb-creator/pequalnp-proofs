import hashlib,importlib.util,json
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
spec=importlib.util.spec_from_file_location('redundancy_core',BASE/'sat-p14-compact-redundancy.py');core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
reports=[]
for suffix,equality,negative_proxy,graph,nine_free,incomparable,partition,empty_opposite,cross,redundancy in [('28-control',False,False,'fano',False,True,False,False,False,False),('-host-control',True,True,'matching',True,False,True,True,True,True)]:
 oldtag='sat-p14-compact-cross'+suffix;tag='sat-p14-compact-redundancy'+suffix
 old=json.loads((BASE/(oldtag+'.metadata.json')).read_text());control=json.loads((BASE/(oldtag+'.compact-control.json')).read_text());A={int(k):bool(v)for k,v in json.loads((BASE/(oldtag+'.complete-assignment.json')).read_text()).items()}
 c,m=core.build(old['cap'],equality,negative_proxy,graph,nine_free,incomparable,partition,empty_opposite,True,cross,redundancy)
 assert m['positive_redundancy']['variable_begin']==old['variables']
 for rows in m['positive_redundancy']['atoms']:
  for entry in rows:
   assert entry['out'] not in A;A[entry['out']]=any(A[t]for t in entry['terms'])
 assert set(A)==set(range(1,m['variables']+1))
 for i,clause in enumerate(c.cs):assert any(A[abs(v)]==(v>0)for v in clause),(tag,i,clause)
 core.quiet.core.validate(control);assert not core.quiet.compact_derivative(control,0,7)and not core.quiet.compact_derivative(control,7,0)
 c.write(BASE/(tag+'.cnf'))
 for ending,obj in [('.metadata.json',m),('.compact-control.json',control),('.complete-assignment.json',A)]:
  (BASE/(tag+ending)).write_text(json.dumps(obj,indent=2)+'\n')
 reports.append(dict(tag=tag,variables=m['variables'],clauses=m['clauses'],positive_redundancy=redundancy,graph=graph,all_truth_rows=16384,marked_derivatives=[False,False]))
c,m=core.build(18,negative_proxy=True);c.write(BASE/'sat-p14-compact-redundancy18-target.cnf');(BASE/'sat-p14-compact-redundancy18-target.metadata.json').write_text(json.dumps(m,indent=2)+'\n')
report=dict(verdict='PASS author complete controls',source_sha256=hashlib.sha256((BASE/'sat-p14-compact-redundancy.py').read_bytes()).hexdigest(),target=dict(variables=m['variables'],clauses=m['clauses'],added_variables=m['variables']-m['positive_redundancy']['variable_begin'],added_clauses=m['clauses']-m['positive_redundancy']['clause_begin']),controls=reports,scope='Positive-support redundancy enabled on hosted matching control, disabled on exact28 Fano control. General justification uses exact27 reconstruction and ordinary Fano lower bound. No solver run or target claim.')
(BASE/'sat-p14-compact-redundancy-controls.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
