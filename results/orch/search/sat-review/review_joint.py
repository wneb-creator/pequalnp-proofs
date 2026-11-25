from pathlib import Path
import json,hashlib,itertools,sys
p=Path('/tmp/oec/pequalnp-pilot-70/constructive');q=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
family=sys.argv[1]
if family=='ten':prod,old,smokeprefix,nvariants,nrows,ngates=('joint-ten10','four-star-cut10-v0','joint-ten11-smoke-v1',6,17,10)
else:prod,old,smokeprefix,nvariants,nrows,ngates=('joint-noncollinear14','noncollinear-cut14-v0','joint-noncollinear15-smoke-v1',7,27,14)
H={(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)}
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def readcnf(path,m):
 lines=path.read_text().splitlines();assert lines[0]==f'p cnf {m["nv"]} {m["clauses"]}'
 ans=[]
 for line in lines[1:]:
  a=list(map(int,line.split()));assert a[-1]==0 and all(1<=abs(v)<=m['nv'] for v in a[:-1]);ans.append(tuple(a[:-1]))
 assert len(ans)==m['clauses'];return ans
def norm(c):return tuple(sorted(set(c),key=abs))
def variable(i,n):
 block=(1<<(1<<i))-1;return sum(block<<(j+(1<<i)) for j in range(0,1<<n,1<<(i+1)))
def sumvec(w,s):
 t=0
 for i in s:t|=w[i]
 return t
def target(w,edges):
 t=0
 for a,b in edges:t|=w[a]&w[b]
 return t
def run(w,gates):
 w=list(w)
 for op,a,b in gates:
  assert op in ('and','or') and 0<=a<=b<len(w)
  w.append(w[a]|w[b] if op=='or' else w[a]&w[b])
 return w
m=json.loads((p/(prod+'.map.json')).read_text());base=json.loads((q/(old+'.map.json')).read_text());cnf=readcnf(p/(prod+'.cnf'),m);bc=readcnf(q/(old+'.cnf'),base)
assert m['format']=='joint-correlated-v1' and m['gates']==ngates and len(m['variants'])==nvariants and len(m['targets'])==nrows
assert sha(p/(prod+'.cnf'))==m['cnf_sha256'] and m['truth']==1 and cnf[0]==(1,)
assert m['lex_order'] and m['allow_initial_repeats'] and m['allow_trivial'] and not m['liveness'] and not m['canonical_prefix']
for idx,v in enumerate(m['variants']):
 path=Path(v['source']);raw=path.read_bytes();assert hashlib.sha256(raw).hexdigest()==v['sha256'] and json.loads(raw)==v['data']
 assert v['data']['variant']==idx
 ordered=sorted(v['data']['rows'],key=lambda r:(not bool(r['value']),r['mask']));assert ordered==v['ordered_rows']
 assert [r['mask'] for r in ordered]==m['ordered_base_masks'] and [r['value'] for r in ordered]==m['targets']
 assert v['data']['real_inputs']==m['variants'][0]['data']['real_inputs'] and v['data']['edges']==m['variants'][0]['data']['edges']
selectors=m['variant_selectors'];first=m['structure'][0]['left'][0];delta=first-2
assert selectors==list(range(2,2+nvariants)) and m['nv']-base['nv']==delta
selector_clause_count=3*(nvariants-2)+2
selclauses=cnf[1:1+selector_clause_count]
aux=list(range(2+nvariants,2+nvariants+nvariants-2))
for mask in range(1<<nvariants):
 witnesses=0
 for av in range(1<<len(aux)):
  a={v:bool(mask>>i&1) for i,v in enumerate(selectors)}|{v:bool(av>>i&1) for i,v in enumerate(aux)}
  witnesses+=all(any(a[abs(l)]==(l>0) for l in c) for c in selclauses)
 assert bool(witnesses)==(mask.bit_count()==1)
expectedcells=[];conditional=[];used=set();const_count=0
for wire,column in enumerate(m['input_values']):
 assert len(column)==nrows
 for r,lit in enumerate(column):
  bits=[v['ordered_rows'][r]['cuts'][wire] for v in m['variants']]
  if len(set(bits))==1:assert lit==(1 if bits[0] else -1);const_count+=1
  else:
   assert lit>1 and lit not in used;used.add(lit)
   expectedcells.append(dict(wire=wire,row=r,variable=lit,bits=bits))
   conditional.extend(norm([-s,lit if bit else -lit]) for s,bit in zip(selectors,bits))
assert expectedcells==m['varying_cells'] and len(conditional)==m['conditional_clause_count']
assert used==set(range(2+nvariants+len(aux),first))
start=1+selector_clause_count
assert cnf[start:start+len(conditional)]==conditional
cutmap={c['variable']:(1 if c['bits'][0] else -1) for c in expectedcells}
def lower(l):
 a=abs(l);v=1 if a==1 else (cutmap[a] if a in cutmap else a-delta)
 assert a==1 or a in cutmap or a>=first
 return v if l>0 else -v
projected=[norm(map(lower,c)) for c in cnf[start+len(conditional):]]
assert projected==[norm(c) for c in bc[1:]], 'Base gate/output clauses changed'
for new,prior in zip(m['structure'],base['structure']):
 for k in prior:
  if k=='op':assert new[k]-delta==prior[k]
  elif isinstance(prior[k],list):assert [v-delta for v in new[k]]==prior[k]
assert m['clauses']==base['clauses']+selector_clause_count+len(conditional)
fv=[variable(i,14) for i in range(14)];ft=target(fv,H)
def checkmodel(mp,cp,lp):
 md=json.loads(mp.read_text());clauses=readcnf(cp,md);assert sha(cp)==md['cnf_sha256']
 lines=lp.read_text().splitlines();assert 's SATISFIABLE' in lines
 a={}
 for line in lines:
  if line.startswith('v '):
   for lit in map(int,line.split()[1:]):
    if lit:
     assert abs(lit) not in a or a[abs(lit)]==(lit>0);a[abs(lit)]=lit>0
 assert set(a)==set(range(1,md['nv']+1))
 def val(l):return a[abs(l)]==(l>0)
 assert all(any(val(l) for l in c) for c in clauses)
 selected=[i for i,s in enumerate(md['variant_selectors']) if a[s]];assert len(selected)==1
 branch=selected[0];v=md['variants'][branch];d=v['data'];cone=[]
 for i,g in enumerate(md['structure']):
  left=[i for i,s in enumerate(g['left']) if a[s]];right=[i for i,s in enumerate(g['right']) if a[s]];assert len(left)==len(right)==1
  cone.append(['or' if a[g['op']] else 'and',left[0],right[0]])
 for rowidx,row in enumerate(v['ordered_rows']):
  initial=row['cuts'];w=run(initial,cone)
  assert w[-1]==row['value']
  for j,b in enumerate(initial):assert val(md['input_values'][j][rowidx])==b
  for i,(g,(_,u,vv)) in enumerate(zip(md['structure'],cone)):
   assert val(g['lv'][rowidx])==w[u] and val(g['rv'][rowidx])==w[vv] and val(g['out'][rowidx])==w[md['ninputs']+i]
 real=d['real_inputs'];rv=[variable(i,real) for i in range(real)];signals=rv+[sumvec(rv,s) for s in d['free_or_supports']]
 assert run(signals,cone)[-1]==target(rv,d['edges'])
 prefix=[['or' if op else 'and',*sorted((u,v))] for op,u,v in d['fixed_gates']];pw=run(fv,prefix)
 for wire,s in zip(d['fixed_cut_wires'],d['free_or_supports']):assert pw[wire]==sumvec(fv,[d['original_variables'][i] for i in s])
 full=list(prefix);mapping=d['original_variables']+d['fixed_cut_wires']
 for op,u,v in cone:full.append([op,*sorted((mapping[u],mapping[v]))]);mapping.append(13+len(full))
 full.append(['or',*sorted((d['fixed_output'],mapping[-1]))]);assert run(fv,full)[-1]==ft
 assert len(full)==len(prefix)+md['gates']+1
 return {'branch':branch,'full_gates':len(full),'clauses':len(clauses),'underlying_inputs':1<<real},full
sm=json.loads((p/(smokeprefix+'-result.json')).read_text());assert sm['all_passed'] and len(sm['results'])==2*nvariants+3
smokebase=json.loads((p/(smokeprefix+'-base.map.json')).read_text());sb=readcnf(p/(smokeprefix+'-base.cnf'),smokebase)
checks=[]
for entry in sm['results']:
 name=entry['name'];stem=smokeprefix+'-'+name;md=json.loads((p/(stem+'.map.json')).read_text());cc=readcnf(p/(stem+'.cnf'),md)
 units=[]
 for (op,u,v),g in zip(md['fixed_smoke_gates'],md['structure']):units.extend([g['left'][u],g['right'][v],g['op'] if op=='or' else -g['op']])
 units+=md['fixed_smoke_units'];assert cc==sb+[(u,) for u in units]
 if entry['expected']=='SAT':
  result,full=checkmodel(p/(stem+'.map.json'),p/(stem+'.cnf'),p/(stem+'.solve.log'))
  if name!='free-selector':assert result['branch']==int(name.split('-')[-1])
  verified=json.loads((p/(stem+'.verified.json')).read_text());assert verified['full_gates']==full and verified['full_gate_count']==27
  checks.append({'name':name,'status':'SAT',**result})
 else:
  assert entry['exit_code']==20 and 's UNSATISFIABLE' in (p/(stem+'.solve.log')).read_text()
  if 'wrong-cut' in name:
   branch=int(name.split('-')[1]);c=md['varying_cells'][0];expected=[md['variant_selectors'][branch],-c['variable'] if c['bits'][branch] else c['variable']];assert md['fixed_smoke_units']==expected
   assert norm([-expected[0],-expected[1]]) in sb
  elif name=='no-selector':assert md['fixed_smoke_units']==[-s for s in md['variant_selectors']]
  elif name=='two-selectors':assert md['fixed_smoke_units']==md['variant_selectors'][:2]
  else:raise AssertionError(name)
  checks.append({'name':name,'status':'UNSAT','reason':'Explicit selector or cut contradiction'})
if family=='ten':
 runner=json.loads((p/'joint-runner-smoke-v1-result.json').read_text());assert runner['status']=='SAT' and runner['full_truth_table_verified'] and runner['full_gate_count']==27
 result,full=checkmodel(p/'joint-ten11-smoke-v1-branch-0.map.json',p/'joint-ten11-smoke-v1-branch-0.cnf',p/'joint-runner-smoke-v1-solve.log')
 assert json.loads((p/'joint-runner-smoke-v1-witness.json').read_text())==full
report={'status':'PASS','family':family,'production_variables':m['nv'],'production_clauses':m['clauses'],'branches':nvariants,'varying_cells':len(expectedcells),'conditional_clauses':len(conditional),'selector_clauses':selector_clause_count,'base_gate_clauses_preserved':len(bc)-1,'smokes':checks,'cnf_sha256':sha(p/(prod+'.cnf')),'source_sha256':{f:sha(p/f) for f in ['joint_correlated.py','joint_decode.py','joint_run.py','joint_smoke.py']}}
Path('joint-'+family+'-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
