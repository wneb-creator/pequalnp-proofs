from pathlib import Path
import hashlib,json,itertools
p=Path('/tmp/oec/pequalnp-pilot-70/constructive');q=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
H={(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)}
V=[0,1,7,8,9,10,13];R={(V.index(a),V.index(b)) for a,b in H if a in (0,1)}
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
rv=[variable(i,7) for i in range(7)];fv=[variable(i,14) for i in range(14)];rt=target(rv,R);ft=target(fv,H)
pos=[m for m in range(128) if (rt>>m)&1 and all(not ((rt>>(m^(1<<i)))&1) for i in range(7) if m>>i&1)]
neg=[m for m in range(128) if not ((rt>>m)&1) and all((rt>>(m|(1<<i)))&1 for i in range(7) if not(m>>i&1))]
assert len(pos)==6 and len(neg)==4
for m in range(128):assert any((a&m)==a for a in pos) if rt>>m&1 else any((m&b)==m for b in neg)
d=json.loads((p/'five-star-cut-cone-rows.json').read_text());adapted=json.loads((q/'five-star-cut-cone-adapted.json').read_text())
assert set(adapted)==set(d)|{'free_or_supports','source_boundary_sha256'}
assert {k:adapted[k] for k in d}==d and adapted['free_or_supports']==d['free_or_sums']
assert adapted['source_boundary_sha256']==hashlib.sha256((p/'five-star-cut-cone-rows.json').read_bytes()).hexdigest()
assert d['real_inputs']==7 and d['cut_inputs']==11 and d['original_variables']==V and {tuple(e) for e in d['edges']}==R
assert d['positive_rows']==pos and d['negative_rows']==neg
supports=d['free_or_sums'];assert supports==[[3,6],[5,6],[4,5],[3,4]]
values=rv+[rv[a]|rv[b] for a,b in supports]
for row in d['rows']:
 m=row['mask'];assert row['cuts']==[(v>>m)&1 for v in values] and row['value']==((rt>>m)&1)
assert len(d['rows'])==10 and {row['mask'] for row in d['rows']}==set(pos+neg)
prefix=d['fixed_gates'];assert len(prefix)==19 and d['fixed_output']==32 and d['fixed_cut_wires']==[14,20,23,26]
pw=run(fv,prefix);assert pw[32]==target(fv,{e for e in H if e[0] not in (0,1)})
for wire,(a,b) in zip(d['fixed_cut_wires'],supports):assert pw[wire]==fv[V[a]]|fv[V[b]]
def embed(a):
 gs=list(prefix);mapping=V+d['fixed_cut_wires']
 for op,u,v in a['gates']:
  gs.append([op,mapping[u],mapping[v]]);mapping.append(13+len(gs))
 gs.append([1,32,mapping[a['output']]])
 return gs
base=json.loads((p/'five-star-cut-cone-baseline7.json').read_text());assert len(base['gates'])==7 and run(values,base['gates'])[base['output']]==rt
assert len(embed(base))==27 and run(fv,embed(base))[-1]==ft
seeds=[]
for edge in [(0,7),(0,8)]:
 a=json.loads((p/f'five-star-cut-cone-seed6-missing-{edge[0]}-{edge[1]}.json').read_text());miss=tuple(a['missing_local_edge']);assert tuple(a['missing_original_edge'])==edge and (V[miss[0]],V[miss[1]])==edge
 assert len(a['gates'])==6 and run(values,a['gates'])[a['output']]==target(rv,R-{miss})
 assert len(embed(a))==26 and run(fv,embed(a))[-1]==target(fv,H-{edge})
 seeds.append({'edge':edge,'residual_misses':(rt^target(rv,R-{miss})).bit_count(),'full_misses':(ft^target(fv,H-{edge})).bit_count()})
s=json.loads((p/'five-star-cut-cone-symmetries.json').read_text());autos=s['permutations'];assert len({tuple(a) for a in autos})==8
for a in autos:
 assert sorted(a)==list(range(11)) and sorted(a[:7])==list(range(7))
 assert {tuple(sorted((a[u],a[v]))) for u,v in R}==R
 for i,(u,v) in enumerate(supports):assert values[a[7+i]]==values[a[u]]|values[a[v]]
assert sorted({min(tuple(sorted((a[u],a[v]))) for a in autos) for u in range(11) for v in range(u,11)})==list(map(tuple,s['all_first_pair_representatives']))
m=json.loads((q/'five-star-cut6.map.json').read_text());assert m['gates']==6 and m['ninputs']==11 and len(m['rows'])==10 and m['nv']==497 and m['clauses']==5489
assert all(not m[k] for k in ['minimal','minimal_prefix','canonical_prefix','liveness','ordered_max','dirty_and','shadow_missing']) and m['prefix'] is None
assert m['allow_initial_repeats'] and m['allow_trivial'] and m['lex_order']
for mask,row in zip(m['correlated']['ordered_base_masks'],m['rows']):assert row==sum(((v>>mask)&1)<<i for i,v in enumerate(values))
assert m['correlated']['ordered_base_masks'][:6]==pos
counts={}
for smoke,basename,status in [('five-star-cut7-smoke','five-star-cut7-smoke-base','SAT'),('five-star-cut6-seed-smoke','five-star-cut6','UNSAT')]:
 sm=json.loads((q/(smoke+'.map.json')).read_text());lines=(q/(smoke+'.cnf')).read_text().splitlines();bl=(q/(basename+'.cnf')).read_text().splitlines();n=len(sm['fixed_smoke_gates']);assert lines[1:-3*n]==bl[1:]
 expected=[]
 for (op,a,b),g in zip(sm['fixed_smoke_gates'],sm['structure']):expected += [g['left'][a],g['right'][b],g['op'] if op=='or' else -g['op']]
 assert lines[-3*n:]==[str(v)+' 0' for v in expected]
 for i,g in enumerate(sm['fixed_smoke_gates']):
  if i and g[2]!=11+i-1:
   old=sm['fixed_smoke_gates'][i-1];assert (old[1],old[2],old[0]=='or')<=(g[1],g[2],g[0]=='or')
 gs=[[int(op=='or'),a,b] for op,a,b in sm['fixed_smoke_gates']];errors=(run(values,gs)[-1]^rt).bit_count();assert (errors==0)==(status=='SAT')
 result=json.loads((q/(smoke+'-result.json')).read_text());assert result['status']==status
 assert result['cnf_sha256']==hashlib.sha256((q/(smoke+'.cnf')).read_bytes()).hexdigest()
 if status=='SAT':
  model={abs(int(v)):int(v)>0 for line in (q/(smoke+'-solve.log')).read_text().splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v)}
  assert len(model)==sm['nv']
  for line in lines[1:]:assert any(model[abs(v)]==(v>0) for v in map(int,line.split()[:-1]))
  w=json.loads((q/(smoke+'-witness.json')).read_text());assert len(w)==27 and run(fv,[[int(op=='or'),a,b] for op,a,b in w])[-1]==ft
  assert result['full_truth_table_verified']
 counts[smoke]={'clauses':len(lines)-1,'status':status,'underlying_mismatches':errors}
assert hashlib.sha256((q/'correlated_family_synthesize.py').read_bytes()).hexdigest()=='347c9231b4b38c609ca7905e6aa2a23a4cd41083122dd4901f751000403c608c'
report={'status':'PASS','candidate_variables':497,'candidate_clauses':5489,'boundary_rows':10,'underlying_inputs_checked':128,'full_inputs_checked':16384,'cut_identities_checked':4,'seed_checks':seeds,'smokes':counts,'source_sha256':{f:hashlib.sha256((q/f).read_bytes()).hexdigest() for f in ['correlated_family_synthesize.py','decode_correlated_flexible.py','run_correlated_flexible.py']},'candidate_cnf_sha256':hashlib.sha256((q/'five-star-cut6.cnf').read_bytes()).hexdigest()}
Path('five-star-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
