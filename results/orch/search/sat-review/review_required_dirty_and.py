from pathlib import Path
import hashlib,json,itertools
q=Path('/tmp/oec/pequalnp-pilot-70/circuit-search');p=Path('/tmp/oec/pequalnp-pilot-70/constructive')
H={(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)}
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def variable(i,n):
 block=(1<<(1<<i))-1;return sum(block<<(j+(1<<i)) for j in range(0,1<<n,1<<(i+1)))
def sumvec(w,s):
 t=0
 for i in s:t|=w[i]
 return t
def target(w,e):
 t=0
 for u,v in e:t|=w[u]&w[v]
 return t
def run(w,gates):
 w=list(w)
 for op,u,v in gates:
  assert op in ('and','or') and 0<=u<len(w) and 0<=v<len(w);w.append(w[u]|w[v] if op=='or' else w[u]&w[v])
 return w
def readcnf(f,m):
 ls=f.read_text().splitlines();assert ls[0]==f'p cnf {m["nv"]} {m["clauses"]}';cs=[list(map(int,l.split()[:-1])) for l in ls[1:]];assert len(cs)==m['clauses'];return cs
fv=[variable(i,14) for i in range(14)];ft=target(fv,H);falsebits=((1<<(1<<14))-1)^ft
reports=[]
for newstem,oldstem,oldpath in [('joint-ten10-live-dirty','joint-ten10-live',q),('joint-noncollinear14-live-dirty','joint-noncollinear14-live',q),('dirty-and28-smoke-dirty','dirty-and28-smoke-live',q),('dirty-and27-clean-smoke-base','joint-ten11-smoke-v1-base',p)]:
 m=json.loads((q/(newstem+'.map.json')).read_text());old=json.loads((oldpath/(oldstem+'.map.json')).read_text());cs=readcnf(q/(newstem+'.cnf'),m);bc=readcnf(oldpath/(oldstem+'.cnf'),old);negative=[i for i,v in enumerate(old['targets']) if not v]
 nv=old['nv'];delta=[];witness=[]
 for i,g in enumerate(old['structure']):
  for r in negative:
   nv+=1;witness.append({'variable':nv,'gate':i,'row':r});delta += [[-nv,-g['op']],[-nv,g['out'][r]]]
 delta.append([d['variable'] for d in witness]);assert cs==bc+delta and nv==m['nv'] and m['required_dirty_and']['witnesses']==witness
 assert m['required_dirty_and']['added_variables']==len(witness) and m['required_dirty_and']['added_clauses']==len(delta)
 assert m['required_dirty_and']['base_sha256']==sha(oldpath/(oldstem+'.cnf')) and m['required_dirty_and']['postprocessor_sha256']==sha(q/'add_required_dirty_and.py')
 assert m['cnf_file']==str((q/(newstem+'.cnf')).resolve()) and m['cnf_sha256']==sha(q/(newstem+'.cnf'))
 changed={'nv','clauses','cnf_file','cnf_sha256','required_dirty_and'};assert {k:v for k,v in m.items() if k not in changed}=={k:v for k,v in old.items() if k not in changed}
 fullcounts=[]
 for variant in old['variants']:
  d=variant['data'];real=d['real_inputs'];V=d['original_variables'];edges={tuple(e) for e in d['edges']};assert {(V[u],V[v]) for u,v in edges}<=H
  rv=[variable(i,real) for i in range(real)];rt=target(rv,edges)
  maxfalse=[mask for mask in range(1<<real) if not(rt>>mask&1) and all(rt>>(mask|(1<<i))&1 for i in range(real) if not(mask>>i&1))]
  assert [variant['ordered_rows'][i]['mask'] for i in negative]==maxfalse
  prefix=[['or' if op else 'and',u,v] for op,u,v in d['fixed_gates']];pw=run(fv,prefix)
  for i,(op,_,_) in enumerate(prefix):
   if op=='and':assert not(pw[14+i]&falsebits)
  for wire,s in zip(d['fixed_cut_wires'],d['free_or_supports']):assert pw[wire]==sumvec(fv,[V[i] for i in s])
  fullcounts.append(len(prefix)+old['gates']+1)
 assert fullcounts==m['required_dirty_and']['full_gate_counts']
 reports.append({'name':newstem,'variables':m['nv'],'clauses':m['clauses'],'new_witness_variables':len(witness),'new_clauses':len(delta),'full_gate_counts':fullcounts,'sha256':sha(q/(newstem+'.cnf'))})
smokes=[]
for stem,basestem,status in [('dirty-and28-smoke','dirty-and28-smoke-dirty','SAT'),('dirty-and27-clean-smoke','dirty-and27-clean-smoke-base','UNSAT')]:
 m=json.loads((q/(stem+'.map.json')).read_text());b=json.loads((q/(basestem+'.map.json')).read_text());cs=readcnf(q/(stem+'.cnf'),m);bc=readcnf(q/(basestem+'.cnf'),b);gs=m['fixed_smoke_gates'];units=[]
 for (op,u,v),g in zip(gs,m['structure']):units += [[g['left'][u]],[g['right'][v]],[g['op'] if op=='or' else -g['op']]]
 units += [[u] for u in m['fixed_smoke_units']];assert cs==bc+units and m['fixed_smoke_units']==[m['variant_selectors'][0]]
 d=m['variants'][0]['data'];real=d['real_inputs'];rv=[variable(i,real) for i in range(real)];signals=rv+[sumvec(rv,s) for s in d['free_or_supports']];rt=target(rv,d['edges']);wv=run(signals,gs);assert wv[-1]==rt
 neg=[i for i,v in enumerate(m['targets']) if not v];dirty=[]
 for i,(op,u,v) in enumerate(gs):
  for r in neg:
   mask=m['ordered_base_masks'][r]
   if op=='and' and wv[m['ninputs']+i]>>mask&1:dirty.append((i,r))
 result=json.loads((q/(stem+'-result.json')).read_text());assert result['status']==status and result['cnf_sha256']==sha(q/(stem+'.cnf'))
 if status=='SAT':
  assert gs[0]==['and',0,0] and dirty and any(m['ninputs'] in (u,v) for _,u,v in gs[1:])
  assignment={abs(int(v)):int(v)>0 for line in (q/(stem+'-solve.log')).read_text().splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v)};assert set(assignment)==set(range(1,m['nv']+1))
  assert all(any(assignment[abs(v)]==(v>0) for v in c) for c in cs)
  for i,g in enumerate(m['structure']):
   for r,mask in enumerate(m['ordered_base_masks']):assert assignment[g['out'][r]]==bool(wv[m['ninputs']+i]>>mask&1)
  full=json.loads((q/(stem+'-witness.json')).read_text());assert len(full)==28 and run(fv,full)[-1]==ft and result['full_truth_table_verified'] and result['full_gate_count']==28
 else:
  assert not dirty and 's UNSATISFIABLE' in (q/(stem+'-solve.log')).read_text()
 smokes.append({'name':stem,'status':status,'clauses':len(cs),'dirty_gate_row_witnesses':len(dirty),'full_gate_count':len(d['fixed_gates'])+len(gs)+1})
report={'status':'PASS','source_sha256':sha(q/'add_required_dirty_and.py'),'smoke_source_sha256':sha(q/'required_dirty_and_smokes.py'),'outputs':reports,'smokes':smokes,'prefix_cleanliness_checked':'Every full false assignment, by bit-vector evaluation for every variant','necessity_scope':'Reviewed fixed-star embeddings with final OR and full gate count <=26, using checked clean-AND27 bound plus residual projection and monotonicity. No unrestricted lower-bound claim or production solve.'}
Path('required-dirty-and-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
