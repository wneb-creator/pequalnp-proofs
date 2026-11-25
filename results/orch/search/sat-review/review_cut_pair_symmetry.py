from pathlib import Path
import json,hashlib,itertools
q=Path('/tmp/oec/pequalnp-pilot-70/circuit-search');p=Path('/tmp/oec/pequalnp-pilot-70/constructive')
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def variable(i,n):
 block=(1<<(1<<i))-1;return sum(block<<(j+(1<<i)) for j in range(0,1<<n,1<<(i+1)))
def sumvec(w,s):
 t=0
 for i in s:t|=w[i]
 return t
def target(w,edges):
 t=0
 for u,v in edges:t|=w[u]&w[v]
 return t
def run(w,gates):
 w=list(w)
 for op,a,b in gates:
  assert op in ('and','or') and 0<=a<=b<len(w)
  w.append(w[a]|w[b] if op=='or' else w[a]&w[b])
 return w
reports=[]
for stem,certname,variant in [('matching-cut14','matching-cut-cone-automorphisms.json',None),('noncollinear-cut14-v0','noncollinear-cut-cone-first-pairs.json',0)]:
 m=json.loads((q/(stem+'.map.json')).read_text());new=json.loads((q/(stem+'-pairs.map.json')).read_text());allcert=json.loads((p/certname).read_text());cert=allcert if variant is None else next(c for c in allcert['variants'] if c['variant']==variant)
 data=m['correlated'];n=m['ninputs'];real=data['real_inputs'];supports=[[i] for i in range(real)]+data.get('free_or_supports',data.get('free_or_sums'));perms=list(map(tuple,cert['permutations']));group=set(perms)
 assert len(group)==len(perms) and tuple(range(n)) in group
 edges={tuple(sorted(e)) for e in m['edges']};rv=[variable(i,real) for i in range(real)];signals=[sumvec(rv,s) for s in supports]
 for a in perms:
  assert sorted(a)==list(range(n)) and sorted(a[:real])==list(range(real))
  assert {tuple(sorted((a[u],a[v]))) for u,v in edges}==edges
  for i,s in enumerate(supports):assert signals[a[i]]==sumvec(signals,[a[v] for v in s])
  for b in perms:assert tuple(a[b[i]] for i in range(n)) in group
 pairs=list(itertools.combinations_with_replacement(range(n),2));representative={pair:min(tuple(sorted((a[pair[0]],a[pair[1]]))) for a in perms) for pair in pairs};reps=sorted(set(representative.values()))
 assert reps==list(map(tuple,cert['all_first_pair_representatives']))==list(map(tuple,new['cut_pair_symmetry']['representatives']))
 g=m['structure'][0];bans=[(-g['left'][u],-g['right'][v]) for u,v in pairs if representative[u,v]!=(u,v)]
 oldlines=(q/(stem+'.cnf')).read_text().splitlines();newlines=(q/(stem+'-pairs.cnf')).read_text().splitlines()
 assert newlines[1:1+len(oldlines)-1]==oldlines[1:]
 assert newlines[len(oldlines):]==[' '.join(map(str,c))+' 0' for c in bans]
 assert new['nv']==m['nv'] and new['clauses']==m['clauses']+len(bans)
 assert newlines[0]==f'p cnf {new["nv"]} {new["clauses"]}'
 assert {k:v for k,v in new.items() if k not in ['clauses','cut_pair_symmetry']}=={k:v for k,v in m.items() if k!='clauses'}
 assert new['cut_pair_symmetry']['base_sha256']==sha(q/(stem+'.cnf')) and new['cut_pair_symmetry']['certificate_sha256']==sha(p/certname)
 assert m['allow_initial_repeats'] and m['allow_trivial'] and not any(m[k] for k in ['liveness','ordered_max','canonical_prefix','minimal','minimal_prefix','shadow_missing','dirty_and'])
 reports.append({'name':stem,'automorphisms':len(group),'pairs_including_repeats':len(pairs),'orbits':len(reps),'bans':len(bans),'variables':m['nv'],'clauses':new['clauses'],'sha256':sha(q/(stem+'-pairs.cnf'))})
stem='matching-cut15-pairs-smoke';m=json.loads((q/(stem+'.map.json')).read_text());base=json.loads((q/(stem+'-base.map.json')).read_text());lines=(q/(stem+'.cnf')).read_text().splitlines();bl=(q/(stem+'-base.cnf')).read_text().splitlines();gates=m['fixed_smoke_gates'];assert lines[1:-3*len(gates)]==bl[1:]
units=[]
for (op,u,v),g in zip(gates,m['structure']):units += [g['left'][u],g['right'][v],g['op'] if op=='or' else -g['op']]
assert lines[-len(units):]==[str(u)+' 0' for u in units]
assert tuple(gates[0][1:]) in list(map(tuple,m['cut_pair_symmetry']['representatives']))
for i,g in enumerate(gates):
 if i and g[2]!=m['ninputs']+i-1:
  old=gates[i-1];assert (old[1],old[2],old[0]=='or')<=(g[1],g[2],g[0]=='or')
model={abs(int(v)):int(v)>0 for line in (q/(stem+'-solve.log')).read_text().splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v)};assert len(model)==m['nv']
for line in lines[1:]:assert any(model[abs(v)]==(v>0) for v in map(int,line.split()[:-1]))
d=m['correlated'];real=d['real_inputs'];rv=[variable(i,real) for i in range(real)];signals=rv+[sumvec(rv,s) for s in d['free_or_sums']];assert run(signals,gates)[-1]==target(rv,d['edges'])
w=json.loads((q/(stem+'-witness.json')).read_text());fv=[variable(i,14) for i in range(14)];H={(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)}
assert len(w)==27 and run(fv,w)[-1]==target(fv,H)
res=json.loads((q/(stem+'-result.json')).read_text());assert res['status']=='SAT' and res['full_truth_table_verified'] and res['cnf_sha256']==sha(q/(stem+'.cnf'))
report={'status':'PASS','static_outputs':reports,'smoke_clauses_verified':len(lines)-1,'smoke_underlying_assignments':1<<real,'smoke_full_assignments':16384,'source_hashes':{name:sha(q/name) for name in ['add_cut_pair_symmetry.py','canonical_cut_seed.py']},'scope':'Fixed correlated family only, output cone pruned and padded, global lex minimum over valid input actions and topological orders.'}
Path('cut-pair-symmetry-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
