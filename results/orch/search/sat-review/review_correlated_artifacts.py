from pathlib import Path
import hashlib,json,runpy
r=runpy.run_path('review_matching_cut.py');root=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
source_names=['correlated_synthesize.py','decode_correlated.py','run_correlated.py','fix_correlated_smoke.py']
meta=json.loads((root/'matching-cut14.map.json').read_text())
assert meta['gates']==14 and meta['ninputs']==13 and len(meta['rows'])==24
assert all(not meta[k] for k in ['minimal','minimal_prefix','canonical_prefix','liveness','ordered_max','dirty_and','shadow_missing'])
assert meta['allow_initial_repeats'] and meta['allow_trivial'] and meta['lex_order']
for mask,row in zip(meta['correlated']['ordered_base_masks'],meta['rows']):assert r['cuts'](mask)==[(row>>i)&1 for i in range(13)]
assert meta['correlated']['ordered_base_masks'][:12]==sorted(r['positive'])
counts={}
for prefix,base_name,expected_status in [('matching-cut15-lex-smoke','matching-cut15-lex-smoke-base','SAT'),('matching-cut14-seed-smoke','matching-cut14','UNSAT')]:
 m=json.loads((root/(prefix+'.map.json')).read_text());base_lines=(root/(base_name+'.cnf')).read_text().splitlines();lines=(root/(prefix+'.cnf')).read_text().splitlines();n=len(m['fixed_smoke_gates'])
 assert lines[1:-3*n]==base_lines[1:]
 expected=[]
 for (op,a,b),g in zip(m['fixed_smoke_gates'],m['structure']):expected += [g['left'][a],g['right'][b],g['op'] if op=='or' else -g['op']]
 assert lines[-3*n:]==[str(v)+' 0' for v in expected]
 for i,g in enumerate(m['fixed_smoke_gates']):
  if i and g[2]!=13+i-1:
   old=m['fixed_smoke_gates'][i-1]
   assert (old[1],old[2],old[0]=='or')<=(g[1],g[2],g[0]=='or')
 result=json.loads((root/(prefix+'-result.json')).read_text());assert result['status']==expected_status
 gs=[[int(op=='or'),a,b] for op,a,b in m['fixed_smoke_gates']]
 errors=sum(r['run'](r['cuts'](mask),gs)[-1]!=r['target'](r['values'](mask,10),r['R']) for mask in range(1024))
 assert errors==(0 if expected_status=='SAT' else 13)
 if expected_status=='SAT':
  literals=[int(w) for line in (root/(prefix+'-solve.log')).read_text().splitlines() if line.startswith('v ') for w in line.split()[1:] if int(w)]
  model={abs(l):l>0 for l in literals};assert len(model)==m['nv']
  for line in lines[1:]:
   cl=list(map(int,line.split()));assert cl[-1]==0
   assert any(model[abs(l)]==(l>0) for l in cl[:-1])
  full=json.loads((root/(prefix+'-witness.json')).read_text());full=[[int(op=='or'),a,b] for op,a,b in full]
  assert len(full)==27
  for mask in range(16384):assert r['run'](r['values'](mask,14),full)[-1]==r['target'](r['values'](mask,14),r['H'])
 counts[prefix]={'clauses':len(lines)-1,'status':expected_status,'residual_mismatches':errors}
report={'status':'passed','source_sha256':{n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in source_names},'candidate_cnf_sha256':hashlib.sha256((root/'matching-cut14.cnf').read_bytes()).hexdigest(),'candidate_variables':meta['nv'],'candidate_clauses':meta['clauses'],'smokes':counts}
Path('correlated-artifacts-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
