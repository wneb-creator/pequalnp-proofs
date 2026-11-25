from pathlib import Path
import hashlib,json,itertools
p=Path('/tmp/oec/pequalnp-pilot-70/constructive');q=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
H={(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)}
F=[0,3,5,6];V=[1,2,4,7,8,9,10,11,12,13];R={(V.index(a),V.index(b)) for a,b in H if a not in F}
def variable(i,n):
 block=(1<<(1<<i))-1;return sum(block<<(j+(1<<i)) for j in range(0,1<<n,1<<(i+1)))
def target(w,edges):
 t=0
 for a,b in edges:t|=w[a]&w[b]
 return t
def sumvec(w,s):
 t=0
 for i in s:t|=w[i]
 return t
def run(w,gs):
 w=list(w)
 for op,a,b in gs:
  assert op in (0,1) and 0<=a<len(w) and 0<=b<len(w)
  w.append((w[a]|w[b]) if op else (w[a]&w[b]))
 return w
rv=[variable(i,10) for i in range(10)];fv=[variable(i,14) for i in range(14)];rt=target(rv,R);ft=target(fv,H)
pos=[m for m in range(1024) if (rt>>m)&1 and all(not ((rt>>(m^(1<<i)))&1) for i in range(10) if m>>i&1)]
neg=[m for m in range(1024) if not ((rt>>m)&1) and all((rt>>(m|(1<<i)))&1 for i in range(10) if not(m>>i&1))]
assert len(pos)==9 and len(neg)==8
for m in range(1024):assert any((a&m)==a for a in pos) if rt>>m&1 else any((m&b)==m for b in neg)
perms=list(itertools.permutations(range(4)))
def act(c,perm):
 d=[None]*4
 for i,x in enumerate(c):d[perm[i]]=perm[x]
 return tuple(d)
allchoices=set(itertools.product(*[[j for j in range(4) if j!=i] for i in range(4)]));seen=set();report=[]
base=json.loads((p/'four-star-cut-cone-baseline11.json').read_text());seeds=[json.loads((p/f'four-star-cut-cone-seed10-missing-1-{b}.json').read_text()) for b in [7,13]]
sym=json.loads((p/'four-star-cut-cone-symmetries.json').read_text())
for idx in range(6):
 d=json.loads((p/f'four-star-cut-cone-variant-{idx}.json').read_text());choice=tuple(d['choice_excluded_neighbor']);orbit={act(choice,s) for s in perms}
 assert set(map(tuple,d['choice_orbit_members']))==orbit and len(orbit)==d['choice_orbit_size'] and choice==min(orbit) and not(seen&orbit);seen|=orbit
 assert d['real_inputs']==10 and d['cut_inputs']==18 and d['original_variables']==V and {tuple(e) for e in d['edges']}==R
 assert d['positive_rows']==pos and d['negative_rows']==neg
 supports=d['free_or_supports'];assert len(supports)==8 and [len(s) for s in supports]==[2,3]*4
 for i,excludedidx in enumerate(choice):
  neighbors={b for a,b in H if a==F[i]};common=neighbors & {b for a,b in H if a==F[excludedidx]};assert len(common)==1
  assert {V[v] for v in supports[2*i]}==neighbors-common and {V[v] for v in supports[2*i+1]}==neighbors
 values=rv+[sumvec(rv,s) for s in supports]
 for row in d['rows']:
  m=row['mask'];assert row['cuts']==[(v>>m)&1 for v in values] and row['value']==((rt>>m)&1)
 assert len(d['rows'])==17 and {row['mask'] for row in d['rows']}==set(pos+neg)
 prefix=d['fixed_gates'];assert len(prefix)==15 and d['fixed_output']==28 and d['fixed_cut_wires']==[14,15,17,18,20,21,23,24]
 pw=run(fv,prefix);assert pw[28]==target(fv,{e for e in H if e[0] in F})
 for wire,s in zip(d['fixed_cut_wires'],supports):assert pw[wire]==sumvec(fv,[V[v] for v in s])
 def embed(a):
  gs=list(prefix);mapping=V+d['fixed_cut_wires']
  for op,u,v in a['gates']:
   gs.append([op,mapping[u],mapping[v]]);mapping.append(13+len(gs))
  gs.append([1,28,mapping[a['output']]])
  return gs
 assert len(base['gates'])==11 and run(values,base['gates'])[base['output']]==rt
 assert len(embed(base))==27 and run(fv,embed(base))[-1]==ft
 errors=[]
 for a in seeds:
  miss=tuple(a['missing_local_edge']);orig=tuple(a['missing_original_edge']);assert (V[miss[0]],V[miss[1]])==orig
  assert len(a['gates'])==10 and run(values,a['gates'])[a['output']]==target(rv,R-{miss})
  assert len(embed(a))==26 and run(fv,embed(a))[-1]==target(fv,H-{orig})
  errors.append({'edge':orig,'residual_misses':(rt^target(rv,R-{miss})).bit_count(),'full_misses':(ft^target(fv,H-{orig})).bit_count()})
 sd=sym['variants'][idx];assert sd['variant']==idx and tuple(sd['choice'])==choice
 autos=sd['cut_signal_stabilizer'];assert len({tuple(a) for a in autos})*len(orbit)==24
 for a in autos:
  assert sorted(a)==list(range(18)) and sorted(a[:10])==list(range(10))
  assert {tuple(sorted((a[u],a[v]))) for u,v in R}==R
  for i,s in enumerate(supports):assert values[a[10+i]]==sumvec(values,[a[v] for v in s])
 report.append({'variant':idx,'orbit_size':len(orbit),'stabilizer':len(autos),'seed_errors':errors})
assert seen==allchoices and len(seen)==81
m=json.loads((q/'four-star-cut10-v0.map.json').read_text());assert m['gates']==10 and m['ninputs']==18 and len(m['rows'])==17
assert all(not m[k] for k in ['minimal','minimal_prefix','canonical_prefix','liveness','ordered_max','dirty_and','shadow_missing']) and m['prefix'] is None
assert m['allow_initial_repeats'] and m['allow_trivial'] and m['lex_order']
d=json.loads((p/'four-star-cut-cone-variant-0.json').read_text());values=rv+[sumvec(rv,s) for s in d['free_or_supports']]
for mask,row in zip(m['correlated']['ordered_base_masks'],m['rows']):assert row==sum(((v>>mask)&1)<<i for i,v in enumerate(values))
assert m['correlated']['ordered_base_masks'][:9]==pos
smoke='four-star-cut11-v0-smoke';sm=json.loads((q/(smoke+'.map.json')).read_text());lines=(q/(smoke+'.cnf')).read_text().splitlines();bl=(q/(smoke+'-base.cnf')).read_text().splitlines();n=len(sm['fixed_smoke_gates']);assert lines[1:-3*n]==bl[1:]
expected=[]
for (op,a,b),g in zip(sm['fixed_smoke_gates'],sm['structure']):expected += [g['left'][a],g['right'][b],g['op'] if op=='or' else -g['op']]
assert lines[-3*n:]==[str(v)+' 0' for v in expected]
for i,g in enumerate(sm['fixed_smoke_gates']):
 if i and g[2]!=18+i-1:
  old=sm['fixed_smoke_gates'][i-1];assert (old[1],old[2],old[0]=='or')<=(g[1],g[2],g[0]=='or')
assert run(values,[[int(op=='or'),a,b] for op,a,b in sm['fixed_smoke_gates']])[-1]==rt
result=json.loads((q/(smoke+'-result.json')).read_text());assert result['status']=='SAT' and result['full_truth_table_verified']
assert result['cnf_sha256']==hashlib.sha256((q/(smoke+'.cnf')).read_bytes()).hexdigest()
model={abs(int(v)):int(v)>0 for line in (q/(smoke+'-solve.log')).read_text().splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v)}
assert len(model)==sm['nv']
for line in lines[1:]:assert any(model[abs(v)]==(v>0) for v in map(int,line.split()[:-1]))
w=json.loads((q/(smoke+'-witness.json')).read_text());assert len(w)==27 and run(fv,[[int(op=='or'),a,b] for op,a,b in w])[-1]==ft
report={'status':'PASS','variants':report,'boundary_rows':17,'underlying_inputs_checked_per_variant':1024,'full_inputs_checked_per_variant':16384,'cut_identities_checked_per_variant':8,'candidate_variables':m['nv'],'candidate_clauses':m['clauses'],'smoke_clauses_verified':len(lines)-1,'source_sha256':{f:hashlib.sha256((q/f).read_bytes()).hexdigest() for f in ['correlated_family_synthesize.py','decode_correlated_flexible.py','run_correlated_flexible.py']},'candidate_cnf_sha256':hashlib.sha256((q/'four-star-cut10-v0.cnf').read_bytes()).hexdigest()}
Path('four-star-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
