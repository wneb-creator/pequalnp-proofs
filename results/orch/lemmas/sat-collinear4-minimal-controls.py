import hashlib,importlib.util,json
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
spec=importlib.util.spec_from_file_location('local_minimal',BASE/'sat-collinear4-minimal.py');local=importlib.util.module_from_spec(spec);spec.loader.exec_module(local)
controls=[x for x in json.loads((BASE/'constructive-collinear4-controls.json').read_text())['controls'] if x.get('excluded_local_point')!=0]
def assign(m,gates,edge):
 A={}
 def put(v,b):assert v not in A;A[v]=bool(b)
 for e,v in zip(m['edges'],m['flags']):put(v,list(e)==list(edge))
 for r in range(2):
  for i,v in enumerate(m['bases'][r]):put(v,i==edge[r])
 masks=m['tests']+[1<<edge[0],1<<edge[1]];vals=[[bool(mask>>i&1) for mask in masks] for i in range(11)];ds=[[i==edge[1],i==edge[0]] for i in range(11)]
 for g,(op,a,b) in zip(m['gates'],gates):
  put(g['op'],op=='and')
  for i,v in enumerate(g['select_a']):put(v,i==a)
  for i,v in enumerate(g['select_b']):put(v,i==b)
  out=[]
  for r,(va,vb,vy) in enumerate(zip(g['selected_a'],g['selected_b'],g['outputs'])):
   put(va,vals[a][r]);put(vb,vals[b][r]);y=vals[a][r] and vals[b][r] if op=='and' else vals[a][r] or vals[b][r];put(vy,y);out.append(y)
  dy=[]
  for r,t in enumerate(g['traces']):
   da,db=ds[a][r],ds[b][r];ta=vals[a][-2+r] and db;tb=da and vals[b][-2+r];both=ta or tb;y=both if op=='and' else da or db
   for name,value in [('selected_a',da),('selected_b',db),('term_a',ta),('term_b',tb),('both',both),('out',y)]:put(t[name],value)
   dy.append(y)
  vals.append(out);ds.append(dy)
 for gate,blocks in zip(m['gates'],m['minimality']['gates']):
  for block in blocks:
   for first,second,terms in [(gate['selected_a'],gate['selected_b'],block['directions'][0]),(gate['selected_b'],gate['selected_a'],block['directions'][1])]:
    for row,v in zip(block['rows'],terms):put(v,A[first[row]] and not A[second[row]])
 assert set(A)==set(range(1,m['variables']+1));return A
reports=[]
symmetry=local.symmetry_check();(BASE/'sat-collinear4-symmetry.json').write_text(json.dumps(symmetry,indent=2)+'\n')
for j,control in enumerate(controls):
 gates=local.local.canonicalize(control['gates']);double=control['kind']=='quiet16';tag='sat-collinear4-minimal-'+('ordinary15' if not double else 'quiet16-'+str(control['excluded_local_point']))+'-control';c,m=local.build(len(gates),double);c.write(BASE/(tag+'.cnf'));(BASE/(tag+'.metadata.json')).write_text(json.dumps(m,indent=2)+'\n')
 cases=[]
 for flag in control['flags']:
  edge=[flag['point_local'],flag['line_local']]
  if tuple(edge) not in local.REPRESENTATIVES:continue
  if double and flag['derivatives']!=[False,False]:continue
  A=assign(m,gates,edge)
  for i,clause in enumerate(c.cs):assert any(A[abs(v)] if v>0 else not A[-v] for v in clause),(tag,edge,i)
  ds=local.validate_local(gates,tuple(edge),double);assert ds==flag['derivatives'];cases.append(dict(edge=edge,derivatives=ds,assignment=A))
 full=local.splice(gates,tuple(cases[0]['edge']));assert full['size']==len(gates)+12
 for case in cases:
  a,b=case['edge'];p=local.ORIGINAL[a];line=7+(-(local.ORIGINAL[b]-7))%7
  assert [local.local.derivative(full['gates'],14,p,line),local.local.derivative(full['gates'],14,line,p)]==case['derivatives']
 result=dict(gates=gates,cases=cases,full_splice=full)
 (BASE/(tag+'.complete-controls.json')).write_text(json.dumps(result)+'\n');reports.append(dict(tag=tag,size=len(gates),variables=m['variables'],clauses=m['clauses'],complete_assignments=len(cases),local_truth_rows=2048,full_splice_size=full['size'],full_truth_rows=16384,marked_pairs_checked=len(cases)))
report=dict(verdict='PASS',encoder_sha256=hashlib.sha256((BASE/'sat-collinear4-minimal.py').read_bytes()).hexdigest(),controls=reports,scope='Author control validation only. Ordinary15 uses doublequiet disabled; quiet16 uses exactly the target restrictions at one extra gate. All four selected orbit representatives have quiet controls; six explicit arm automorphisms cover all12 edges. No local15 quiet witness or solver result.')
(BASE/'sat-collinear4-minimal-controls.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
