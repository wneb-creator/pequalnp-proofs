import json,hashlib,datetime
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-81')
repo=Path('/workspace/pequalnp-proofs/results/orch/lemmas')
def canonical(gs):
 todo=dict(enumerate(gs)); mapping={i:i for i in range(14)}; out=[]
 while todo:
  ready=[]
  for j,(op,a,b) in todo.items():
   if a in mapping and b in mapping:
    aa,bb=sorted((mapping[a],mapping[b]));ready.append(((bb,aa,0 if op=='and' else 1,j),j,op,aa,bb))
  _,j,op,a,b=min(ready);mapping[14+j]=14+len(out);out.append([op,a,b]);del todo[j]
 return out
control=json.loads((repo/'stochastic-high35-p14-control.json').read_text());g35=canonical(control['gates'])
(base/'sat-p14-canonical35-control.json').write_text(json.dumps(dict(inputs=14,gates=g35,output=48),indent=2)+'\n')
gs=[];terms=[]
for i in range(7):
 a=14+len(gs);gs.append(['and',i,7+i]);b=14+len(gs);gs.append(['and',i,7+i]);terms.append(14+len(gs));gs.append(['and',a,b])
out=terms[0]
for w in terms[1:]:gs.append(['or',out,w]);out=14+len(gs)-1
g27=canonical(gs)
(base/'sat-p14-matching27-structural-control.json').write_text(json.dumps(dict(inputs=14,gates=g27,output=40,target='matching, not Fano; structural clauses only'),indent=2)+'\n')
def evaluate(gates,mask):
 v=[bool(mask>>i&1) for i in range(14)]
 for op,a,b in gates:v.append(v[a] and v[b] if op=='and' else v[a] or v[b])
 return v
for mask in range(1<<14):
 assert evaluate(g35,mask)[-1]==any(mask>>p&1 and mask>>(7+l)&1 for p in range(7) for l in range(7) if (p-l)%7 in (0,1,3))
 assert evaluate(g27,mask)[-1]==any(mask>>p&1 and mask>>(7+p)&1 for p in range(7))
def assignment_for(meta,gates):
 assignment={}
 def put(v,b):
  assert type(v)==int and v not in assignment
  assignment[v]=bool(b)
 vals=[[bool(m>>i&1) for m in meta['tests']] for i in range(14)]
 ders=[[i==7,i==0] for i in range(14)]
 for j,(op,a,b) in enumerate(gates):
  assert 0<=a<b<14+j
  z=meta['gates'][j];put(z['op'],op=='and')
  for i,v in enumerate(z['select_a']):put(v,i==a)
  for i,v in enumerate(z['select_b']):put(v,i==b)
  vy=[]
  for r in range(len(meta['tests'])):
   av,bv=vals[a][r],vals[b][r];yv=av and bv if op=='and' else av or bv
   put(z['selected_a'][r],av);put(z['selected_b'][r],bv);put(z['outputs'][r],yv);vy.append(yv)
  dy=[]
  for r,t in enumerate(z['traces']):
   k=meta['tests'].index(meta['bases'][r]);av,bv=vals[a][k],vals[b][k];da,db=ders[a][r],ders[b][r];ta,tb=av and db,da and bv;both=ta or tb;out=both if op=='and' else da or db
   for key,val in [('selected_a',da),('selected_b',db),('term_a',ta),('term_b',tb),('both',both),('out',out)]:put(t[key],val)
   dy.append(out)
  vals.append(vy);ders.append(dy)
 for item in meta['boundary_essential']:
  g=meta['gates'][item['gate']];r=item['row'];a=assignment[g['selected_a'][r]];b=assignment[g['selected_b'][r]]
  put(item['a_not_b'],a and not b);put(item['b_not_a'],b and not a)
 def literal(v):return v if type(v)==bool else assignment[abs(v)] if v>0 else not assignment[-v]
 def dp_fill(dp):
  bits=[literal(x) for x in dp['literals']]
  for c in dp['cells']:put(c['var'],sum(bits[:c['prefix']])>=c['threshold'])
 for item in meta['false_or_count']:
  for j,q in enumerate(item['gate_literals']):put(q,gates[j][0]=='or' and not vals[14+j][item['row']])
  dp_fill(item['dp'])
 for item in meta['p14_branches']:dp_fill(item['dp'])
 for item in meta['p14_eligible']:
  for w,q in enumerate(item['options']):put(q,literal(meta['p14_branches'][w]['dp']['root']) and vals[w][item['row']])
 for item in meta['p14_equality']:
  for j,q in enumerate(item['exits']):
   op,a,b=gates[j];put(q,op=='and' and (vals[a][item['row']] or vals[b][item['row']]))
  dp_fill(item['dp'])
 assert len(assignment)==meta['variables']
 return assignment
reports=[]
for tag,gates,full in [('sat-fano-p14-35control',g35,True),('sat-fano-p14-27',g27,False)]:
 meta=json.loads((base/(tag+'.metadata.json')).read_text());assignment=assignment_for(meta,gates);lo,hi=meta['p14_clause_range'];checked=0;count=0
 with (base/(tag+'.cnf')).open() as f:
  assert f.readline().split()==['p','cnf',str(meta['variables']),str(meta['clauses'])]
  for i,line in enumerate(f):
   cs=list(map(int,line.split()))[:-1];count+=1
   if full or lo<=i<hi:
    assert any(assignment[abs(x)] if x>0 else not assignment[abs(x)] for x in cs),(tag,i,cs)
    checked+=1
 assert count==meta['clauses']
 fanout=[sum(a==w for _,a,b in gates)+sum(b==w for _,a,b in gates) for w in range(14+len(gates))]
 assert all(any(fanout[w]>=2 and evaluate(gates,1<<x)[w] for w in range(len(fanout))) for x in range(14))
 reports.append(dict(tag=tag,variables=len(assignment),clauses_checked=checked,scope='All CNF clauses; exact Fano and p14, equality cuts disabled' if full else 'Only p14 equality extension; exact matching graph, NOT Fano'))
report=dict(verdict='PASS',source_sha256=hashlib.sha256((base/'sat-fano-p14.py').read_bytes()).hexdigest(),controls=reports,full_truth_assignments_each=16384)
(base/'sat-p14-control-test.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
