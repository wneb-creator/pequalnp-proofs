from pathlib import Path
import json,hashlib
p=Path('/tmp/oec/pequalnp-pilot-70/constructive');q=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
H=[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)];C=[e for e in H if 13 not in e]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def variable(i,n):
 block=(1<<(1<<i))-1;return sum(block<<(j+(1<<i)) for j in range(0,1<<n,1<<(i+1)))
def target(w,edges):
 t=0
 for u,v in edges:t|=w[u]&w[v]
 return t
def run(w,gs):
 w=list(w)
 for op,u,v in gs:
  assert op in ('and','or') and 0<=u<=v<len(w);w.append(w[u]|w[v] if op=='or' else w[u]&w[v])
 return w
fv=[variable(i,14) for i in range(14)];targetv=target(fv,H);corev=target(fv,C)
positive=[(1<<a)|(1<<b) for a,b in H];negative=[mask for mask in range(1<<14) if not(targetv>>mask&1) and all(targetv>>(mask|(1<<i))&1 for i in range(14) if not(mask>>i&1))]
assert len(positive)==21 and len(negative)==37
review=json.loads((q/'repair-review.json').read_text());assert review['verdict']=='PASS' and sha(q/'repair_base.py')==review['hashes']['repair_base.py']
def cnf(path,m):
 lines=path.read_text().splitlines();assert lines[0]==f'p cnf {m["nv"]} {m["clauses"]}'
 cs=[list(map(int,l.split()[:-1])) for l in lines[1:]];assert len(cs)==m['clauses'];return cs
productions=[]
for stem,base in [('anchored-tail26','anchored-tail26-base'),('anchored-tail27-smoke-base','anchored-tail27-smoke-base-base')]:
 m=json.loads((p/(stem+'.map.json')).read_text());b=json.loads((p/(base+'.map.json')).read_text());cs=cnf(p/(stem+'.cnf'),m);bc=cnf(p/(base+'.cnf'),b);N=m['gates'];s=m['structure'];meta=m['anchored_tail']
 assert b['rows']==positive+negative and b['edges']==[list(e) for e in H]
 assert b['allow_trivial'] and b['allow_initial_repeats'] and b['prefix'] is None
 assert not any(b[k] for k in ['canonical_prefix','lex_order','liveness','ordered_max','minimal','minimal_prefix','shadow_missing','dirty_and'])
 assert m['base_encoder_sha256']==sha(q/'repair_base.py') and m['source_sha256']==sha(p/'anchored_tail.py') and m['base_cnf_sha256']==sha(p/(base+'.cnf')) and m['cnf_sha256']==sha(p/(stem+'.cnf'))
 assert cs[:len(bc)]==bc and m['structure']==b['structure'] and m['rows']==b['rows']
 expected=[];nv=b['nv'];aux=[]
 for i in range(1,N-2):
  old,new=s[i-1],s[i];el,er=nv+1,nv+2;nv+=2;aux.append([i,el,er]);dep=new['right'][-1]
  for u in range(14+i-1):
   expected += [[-old['left'][u],-new['left'][u],el],[-old['right'][u],-new['right'][u],er]]
   for v in range(u):expected += [[dep,-old['left'][u],-new['left'][v]],[dep,-el,-old['right'][u],-new['right'][v]]]
  expected.append([dep,-el,-er,-old['op'],new['op']])
 penult=14+N-2
 expected += [[-s[-2]['op']],[s[-1]['op']],[s[-1]['right'][penult]],[-s[-1]['left'][penult]]]
 anchor=[]
 for u,v in C:
  mask=(1<<u)|(1<<v);row=b['rows'].index(mask)
  for wire,select in enumerate(s[-1]['left'][:penult]):
   if wire<14:
    if wire not in (u,v):anchor.append([-select])
   else:anchor.append([-select,s[wire-14]['out'][row]])
 expected+=anchor;assert cs[len(bc):]==expected and nv==m['nv']
 assert meta['lex_aux']==aux and meta['prefix_gates']==N-2 and meta['anchor_clauses']==len(anchor) and meta['added_clauses']==len(expected)
 assert meta['core_edges']==[list(e) for e in C] and meta['core_rows']==[(1<<u)|(1<<v) for u,v in C]
 assert len(aux)==N-3 and max(i for i,_,_ in aux)==N-3
 productions.append({'name':stem,'gates':N,'variables':m['nv'],'clauses':m['clauses'],'prefix_lex_comparisons':len(aux),'anchor_clauses':len(anchor),'sha256':sha(p/(stem+'.cnf'))})
witnesses=[]
for name,missing in [('anchored-tail-baseline27',None)]+[(f'anchored-tail-seed26-missing-{i}-13',(i,13)) for i in (1,2,4)]:
 d=json.loads((p/(name+'.json')).read_text());gs=d['gates'];vals=run(fv,gs);wanted=target(fv,[e for e in H if e!=missing]);assert vals[-1]==wanted and vals[d['core_wire']]==corev
 assert len(gs)==(27 if missing is None else 26) and d['prefix_gates']==len(gs)-2
 assert gs[-2][0]=='and' and gs[-1][0]=='or' and gs[-1][1]==d['core_wire'] and gs[-1][2]==14+len(gs)-2
 errors=[m for m in range(1<<14) if (vals[-1]^targetv)>>m&1];assert d['target_error_masks']==errors and d['target_error_count']==len(errors)
 for i,g in enumerate(gs[:len(gs)-2]):
  if i and g[2]!=14+i-1:
   old=gs[i-1];assert (old[1],old[2],old[0]=='or')<=(g[1],g[2],g[0]=='or')
 witnesses.append({'name':name,'full_gates':len(gs),'target_errors':len(errors),'exact_core':True})
stem='anchored-tail27-smoke';m=json.loads((p/(stem+'.map.json')).read_text());bm=json.loads((p/(stem+'-base.map.json')).read_text());cs=cnf(p/(stem+'.cnf'),m);bc=cnf(p/(stem+'-base.cnf'),bm)
baseline=json.loads((p/'anchored-tail-baseline27.json').read_text());units=[]
for (op,u,v),g in zip(baseline['gates'],m['structure']):units += [[g['left'][u]],[g['right'][v]],[g['op'] if op=='or' else -g['op']]]
assert cs==bc+units and m['fixed_witness_sha256']==sha(p/'anchored-tail-baseline27.json')
lines=(p/(stem+'-solve.log')).read_text().splitlines();assert 's SATISFIABLE' in lines
assignment={}
for line in lines:
 if line.startswith('v '):
  for v in map(int,line.split()[1:]):
   if v:assert abs(v) not in assignment or assignment[abs(v)]==(v>0);assignment[abs(v)]=v>0
assert set(assignment)==set(range(1,m['nv']+1))
assert all(any(assignment[abs(v)]==(v>0) for v in c) for c in cs)
gs=[]
for g in m['structure']:
 left=[i for i,v in enumerate(g['left']) if assignment[v]];right=[i for i,v in enumerate(g['right']) if assignment[v]];assert len(left)==len(right)==1
 gs.append(['or' if assignment[g['op']] else 'and',left[0],right[0]])
assert gs==baseline['gates'];values=run(fv,gs);assert values[-1]==targetv and values[gs[-1][1]]==corev
for i,g in enumerate(m['structure']):
 for r,mask in enumerate(m['rows']):assert assignment[g['out'][r]]==bool(values[14+i]>>mask&1)
verified=json.loads((p/(stem+'-verified.json')).read_text());assert verified['status']=='VERIFIED' and verified['gates']==gs and verified['checked_clauses']==len(cs) and verified['checked_assignments']==16384
assert verified['log_sha256']==sha(p/(stem+'-solve.log')) and verified['cnf_sha256']==sha(p/(stem+'.cnf'))
report={'status':'PASS','source_sha256':sha(p/'anchored_tail.py'),'base_encoder_sha256':sha(q/'repair_base.py'),'production_checks':productions,'witness_checks':witnesses,'smoke_cnf_clauses_verified':len(cs),'full_inputs_checked_per_witness':16384,'scope':'Restricted sufficient C OR (U AND V) family, F0 <= C <= Heawood, lex within prefix only; no unrestricted lower-bound claim.'}
Path('anchored-tail-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
