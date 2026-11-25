from pathlib import Path
import json,itertools,hashlib
p=Path('/tmp/oec/pequalnp-pilot-70/constructive');q=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
H={(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)}
V=[3,4,5,6,7,8,9,10,11,12,13];R={(V.index(a),V.index(b)) for a,b in H if a>=3}
def variable(i,n):
 block=(1<<(1<<i))-1;return sum(block<<(j+(1<<i)) for j in range(0,1<<n,1<<(i+1)))
def target(w,edges):
 t=0
 for a,b in edges:t|=w[a]&w[b]
 return t
def run(w,gs):
 w=list(w)
 for op,a,b in gs:
  assert op in (0,1) and 0<=a<len(w) and 0<=b<len(w)
  w.append((w[a]|w[b]) if op else (w[a]&w[b]))
 return w
rv=[variable(i,11) for i in range(11)];fv=[variable(i,14) for i in range(14)];rt=target(rv,R);ft=target(fv,H)
pos=[m for m in range(2048) if (rt>>m)&1 and all(not ((rt>>(m^(1<<i)))&1) for i in range(11) if m>>i&1)]
neg=[m for m in range(2048) if not ((rt>>m)&1) and all((rt>>(m|(1<<i)))&1 for i in range(11) if not(m>>i&1))]
assert len(pos)==12 and len(neg)==15
for m in range(2048):assert any((a&m)==a for a in pos) if rt>>m&1 else any((m&b)==m for b in neg)
base=json.loads((p/'noncollinear-cut-cone-baseline15.json').read_text());seeds=[json.loads(f.read_text()) for f in sorted(p.glob('noncollinear-cut-cone-seed14-missing-*.json'))];assert len(seeds)==4
perms=list(itertools.permutations(range(3)))
def act(c,perm):
 d=[None]*3
 for i,x in enumerate(c):d[perm[i]]=-1 if x==-1 else perm[x]
 return tuple(d)
allchoices=set(itertools.product(*[[-1]+[j for j in range(3) if j!=i] for i in range(3)]));seen=set();report=[]
for idx in range(7):
 d=json.loads((p/f'noncollinear-cut-cone-variant-{idx}.json').read_text());choice=tuple(d['choice_excluded']);orbit={act(choice,s) for s in perms}
 assert set(map(tuple,d['choice_orbit_members']))==orbit and choice==min(orbit) and not(seen&orbit)
 seen|=orbit
 assert d['real_inputs']==11 and d['cut_inputs']==17 and d['original_variables']==V and {tuple(e) for e in d['edges']}==R
 assert d['positive_rows']==pos and d['negative_rows']==neg
 prefix=d['fixed_gates'];assert len(prefix)==11
 supports=d['free_or_supports'];assert len(supports)==6 and [len(s) for s in supports]==[2,3]*3
 for center,selected in enumerate(choice):
  neighbors={b for a,b in H if a==center}
  if selected==-1:
   excluded=next(b for b in neighbors if sum((a,b) in H for a in range(3))==1)
  else:
   common=neighbors & {b for a,b in H if a==selected};assert len(common)==1;excluded=next(iter(common))
  assert {V[i] for i in supports[2*center]}==neighbors-{excluded}
  assert {V[i] for i in supports[2*center+1]}==neighbors
 cuts=[]
 for s in supports:
  assert len(set(s))==len(s) and all(0<=i<11 for i in s)
  v=0
  for i in s:v|=rv[i]
  cuts.append(v)
 values=rv+cuts
 for row in d['rows']:
  m=row['mask'];assert row['cuts']==[(v>>m)&1 for v in values] and row['value']==((rt>>m)&1)
 assert {row['mask'] for row in d['rows']}==set(pos+neg)
 pw=run(fv,prefix);assert pw[24]==target(fv,{e for e in H if e[0]<3})
 for wire,s in zip(d['fixed_cut_wires'],supports):
  want=0
  for i in s:want|=fv[V[i]]
  assert pw[wire]==want
 assert d['fixed_cut_wires']==[14,15,17,18,20,21]
 def embed(a):
  gs=list(prefix);mapping=V+d['fixed_cut_wires']
  for op,u,v in a['gates']:
   gs.append([op,mapping[u],mapping[v]]);mapping.append(13+len(gs))
  gs.append([1,24,mapping[a['output']]])
  return gs
 assert run(values,base['gates'])[base['output']]==rt and len(base['gates'])==15
 full=embed(base);assert len(full)==27 and run(fv,full)[-1]==ft
 errors=[]
 for a in seeds:
  miss=tuple(a['missing_local_edge']);orig=tuple(a['missing_original_edge'])
  assert (V[miss[0]],V[miss[1]])==orig
  assert run(values,a['gates'])[a['output']]==target(rv,R-{miss})
  full=embed(a);assert len(full)==26 and run(fv,full)[-1]==target(fv,H-{orig})
  errors.append({'edge':orig,'residual_misses':(rt^target(rv,R-{miss})).bit_count(),'full_misses':(ft^target(fv,H-{orig})).bit_count()})
 report.append({'variant':idx,'choice':choice,'orbit_size':len(orbit),'seed_errors':errors})
assert seen==allchoices and len(seen)==27
m=json.loads((q/'noncollinear-cut14-v0.map.json').read_text());assert m['gates']==14 and m['ninputs']==17 and len(m['rows'])==27
assert all(not m[k] for k in ['minimal','minimal_prefix','canonical_prefix','liveness','ordered_max','dirty_and','shadow_missing'])
assert m['allow_initial_repeats'] and m['allow_trivial'] and m['lex_order']
for mask,row in zip(m['correlated']['ordered_base_masks'],m['rows']):
 d=json.loads((p/'noncollinear-cut-cone-variant-0.json').read_text())
 original=next(r for r in d['rows'] if r['mask']==mask)
 assert row==sum(v<<i for i,v in enumerate(original['cuts']))
smoke='noncollinear-cut15-v0-smoke';sm=json.loads((q/(smoke+'.map.json')).read_text());lines=(q/(smoke+'.cnf')).read_text().splitlines();bl=(q/(smoke+'-base.cnf')).read_text().splitlines();assert lines[1:-45]==bl[1:]
model={abs(int(v)):int(v)>0 for line in (q/(smoke+'-solve.log')).read_text().splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v)}
for line in lines[1:]:assert any(model[abs(v)]==(v>0) for v in map(int,line.split()[:-1]))
w=json.loads((q/(smoke+'-witness.json')).read_text());assert run(fv,[[int(op=='or'),a,b] for op,a,b in w])[-1]==ft
res={'status':'passed','variants':report,'boundary_rows':27,'underlying_inputs_checked_per_variant':2048,'full_inputs_checked_per_variant':16384,'full_cut_identities_checked_per_variant':6,'choice_count':27,'choice_orbits':7,'candidate_variables':m['nv'],'candidate_clauses':m['clauses'],'candidate_sha256':hashlib.sha256((q/'noncollinear-cut14-v0.cnf').read_bytes()).hexdigest(),'smoke_clauses_verified':len(lines)-1,'source_hashes':{f:hashlib.sha256((q/f).read_bytes()).hexdigest() for f in ['correlated_family_synthesize.py','decode_correlated_family.py','run_correlated_family.py']}}
Path('noncollinear-review.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({k:v for k,v in res.items() if k!='variants'},indent=2))
