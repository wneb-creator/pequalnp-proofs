import importlib.util,itertools,json,hashlib,sys
from pathlib import Path
assert len(sys.argv)==2, 'usage: constructive-compact-audit-portable.py ARTIFACT_DIRECTORY'
base=Path(sys.argv[1]).resolve()
assert base.is_dir()
spec=importlib.util.spec_from_file_location('compact',base/'sat-p14-compact.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
checks=0
for n in range(1,6):
 for k in range(1,n+2):
  c=m.CNF();xs=[c.var() for _ in range(n)];dp=c.threshold(xs,k)
  for bits in itertools.product([False,True],repeat=n):
   a=dict(zip(xs,bits))
   for cell in dp['cells']:a[cell['var']]=sum(bits[:cell['prefix']])>=cell['threshold']
   lit=lambda z:z if type(z)==bool else (a[abs(z)] if z>0 else not a[abs(z)])
   assert all(any(lit(z) for z in row) for row in c.cs)
   assert lit(dp['root'])==(sum(bits)>=k)
   checks+=1
A=[]
def add(S,T,U,V,mode=0):
 A.append(dict(slots=[dict(primary=S,prior=T),dict(primary=U,prior=V)],mode=mode));return len(A)-1
q=add([0],[],[7],[],2)
a=add([1],[q],[8],[]);aa=add([],[a],[8],[])
b=add([1],[q],[0],[]);bb=add([],[b],[7],[])
F=[aa,bb]
for i in range(2,7):
 q=add([i],[],[7+i],[]);u=add([],[q],[i],[]);v=add([],[u],[7+i],[]);F.append(v)
control=dict(atoms=A,final=F,graph='matching',equality=True,negative_proxy=True)
assert len(A)==20;m.validate(control)
c,meta=m.build(21,True,True,'matching');assignment={}
for j,a in enumerate(meta['atoms']):
 active=j<len(A);assignment[a['active']]=active
 for side,s in enumerate(a['slots']):
  chosen=A[j]['slots'][side] if active else dict(primary=[],prior=[])
  for x,z in enumerate(s['primary']):assignment[z]=x in chosen['primary']
  for k,z in enumerate(s['prior']):assignment[z]=k in chosen['prior']
 for mode,z in enumerate(a['modes']):assignment[z]=active and mode==A[j]['mode']
 assignment[meta['final'][j]]=j in F
for dp in [x['dp'] for x in meta['primary_counts']]+[a['use_dp'] for a in meta['atoms']]:
 for cell in dp['cells']:assignment[cell['var']]=sum(assignment[z] for z in dp['literals'][:cell['prefix']])>=cell['threshold']
for j,a in enumerate(meta['atoms']):
 for side,s in enumerate(a['slots']):
  for row,mask in enumerate(meta['tests']):
   for k,z in enumerate(s['terms'][row]):assignment[z]=assignment[s['prior'][k]] and assignment[meta['atoms'][k]['values'][row]]
   assignment[s['values'][row]]=any(assignment[z] and (mask>>x&1) for x,z in enumerate(s['primary'])) or any(assignment[z] for z in s['terms'][row])
 for row,z in enumerate(a['values']):assignment[z]=assignment[a['slots'][0]['values'][row]] and assignment[a['slots'][1]['values'][row]]
for row,z in enumerate(meta['final_values']):
 for j,t in enumerate(meta['final_terms'][row]):assignment[t]=assignment[meta['final'][j]] and assignment[meta['atoms'][j]['values'][row]]
 assignment[z]=any(assignment[t] for t in meta['final_terms'][row])
assert set(assignment)==set(range(1,c.n+1))
failed=[i for i,row in enumerate(c.cs) if not any(assignment[abs(z)]==(z>0) for z in row)]
assert not failed,failed[:5]
report=dict(verdict='PASS',source_sha256=hashlib.sha256((base/'sat-p14-compact.py').read_bytes()).hexdigest(),threshold_ground_cases=checks,host_control_active_atoms=20,host_control_cap=21,host_control_full_truth_rows=16384,host_control_boundary_rows=len(meta['tests']),host_control_variables=c.n,host_control_clauses=len(c.cs),clauses_failed=len(failed),negative_proxy_enabled=True)
(base/'constructive-compact-host-control.json').write_text(json.dumps(control,indent=2)+'\n')
(base/'constructive-compact-encoder-review.json').write_text(json.dumps(report,indent=2)+'\n')
c.write(base/'sat-p14-compact-host-control.cnf')
(base/'sat-p14-compact-host-control.metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
(base/'sat-p14-compact-host-control.complete-assignment.json').write_text(json.dumps({str(k):bool(v) for k,v in assignment.items()},sort_keys=True)+'\n')
print(json.dumps(report))
