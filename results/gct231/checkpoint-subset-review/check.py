from pathlib import Path
import hashlib,json,ast,difflib
import sympy as S
root=Path(__file__).resolve().parents[1];base=root/'sparse-engine';dest=Path(__file__).parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
prov=json.loads((base/'checkpoint-subset/provenance.json').read_text())
assert prov['parent_provenance_sha256']==digest(base/'checkpoint/provenance.json')
for name,h in prov['files'].items():assert digest(base/name)==h,name
print('PASS',len(prov['files']),'provenance hashes and parent provenance',flush=True)
for name in ['gb.c','f4.c','la_qq.c','convert.c']:
    assert (base/f'checkpoint/engine/{name}').read_bytes()==(base/f'checkpoint-subset/engine/{name}').read_bytes()
assert (base/'checkpoint/neogb_cli_checkpoint.c').read_bytes()==(base/'checkpoint-subset/neogb_cli_checkpoint.c').read_bytes()
assert (base/'checkpoint_basis_subset.c').read_bytes()==(base/'checkpoint-subset/engine/checkpoint_basis.c').read_bytes()
assert (base/'run_neogb_checkpoint_subset.py').read_text()==(base/'run_neogb_checkpoint.py').read_text().replace("directory=Path(__file__).parent/'checkpoint'","directory=Path(__file__).parent/'checkpoint-subset'")
delta=''.join(difflib.unified_diff((base/'checkpoint_basis.c').read_text().splitlines(True),(base/'checkpoint_basis_subset.c').read_text().splitlines(True)))
(dest/'source-diff.txt').write_text(delta)
print('PASS solver core, wrapper, runner unchanged except isolated path; export delta saved',flush=True)

# Reuse only three parser functions from our own frozen independent review.
tree=ast.parse((root/'checkpoint_review/check.py').read_text())
selected=ast.Module(body=[node for node in tree.body if isinstance(node,ast.FunctionDef) and node.name in ('parse_input','polynomials','canonical')],type_ignores=[])
assert len(selected.body)==3
exec(compile(selected,'independent-parser-functions','exec'))
totals={'snapshots':0,'consequences':0,'completed_bases':0,'omitting_latest':0}
for engine,budget in [('checkpoint-subset',1000000),('checkpoint-subset-budget2',2)]:
 controls=base/engine/'controls'
 for name in ['unit','nonunit','rational']:
  for prime in [101,1009,65537]:
   input_path=controls/f'{name}-p{prime}.in';n,p,lens,tables=parse_input(input_path)
   xs,polys=polynomials(tables,n,p);ideal=S.groebner([x.as_expr() for x in polys],*xs,modulus=p,order='grevlex')
   for mode in ['full','stop1','resumed']:
    stem=f'{name}-p{prime}-{mode}';result=json.loads((controls/(stem+'.result.json')).read_text())
    assert result['base_input_sha256']==digest(input_path)
    assert result['binary_sha256']==prov['files'][engine+'/neogb_cli_checkpoint']
    assert result['library_sha256']==prov['files'][engine+'/libneogb_checkpoint.so']
    meta=result['checkpoint']['metadata']
    assert meta['derived_term_budget']==budget and 0<=meta['appended_basis_terms']<=budget
    assert meta['available_basis_rows']==meta['appended_basis_rows']+meta['omitted_basis_rows']
    assert meta['available_basis_terms']==meta['appended_basis_terms']+meta['omitted_basis_terms']
    assert meta['omitted_basis_rows']>=0 and meta['omitted_basis_terms']>=0
    totals['omitting_latest']+=meta['omitted_basis_terms']>0
    latest=Path(result['checkpoint']['path']);nn,pp,ll,tt=parse_input(latest)
    assert meta['appended_basis_rows']==len(tt)-len(tables)
    assert meta['appended_basis_terms']==sum(ll[len(lens):])
    assert result['checkpoint']['sha256']==digest(latest)
    for snapshot in sorted(controls.glob(stem+'.checkpoint.s*.in')):
     nn,pp,ll,tt=parse_input(snapshot);assert (nn,pp)==(n,p) and ll[:len(lens)]==lens and tt[:len(tables)]==tables
     assert sum(ll[len(lens):])<=budget
     _,extra=polynomials(tt[len(tables):],n,p)
     for polynomial in extra:assert ideal.reduce(polynomial.as_expr())[1]==0
     totals['snapshots']+=1;totals['consequences']+=len(extra)
    if result['status']=='COMPLETED':
     out=controls/(stem+'.basis.json');data=json.loads(out.read_text())
     ts=[{tuple(e):int(c)%p for c,e in row} for row in data['basis']]
     _,actual=polynomials(ts,n,p);assert canonical(actual)==canonical(ideal.polys)
     assert result['output_sha256']==digest(out)
     totals['completed_bases']+=1
    else:assert mode=='stop1' and result['status']=='STOPPED_AFTER_CHECKPOINT'
   print('PASS controls',engine,name,prime,flush=True)

# Check actual omission policy against the full active basis at the same stop.
for name in ['unit','nonunit','rational']:
 for prime in [101,1009,65537]:
  stem=f'{name}-p{prime}-stop1.result.json'
  full=json.loads((base/'checkpoint-subset/controls'/stem).read_text())
  small=json.loads((base/'checkpoint-subset-budget2/controls'/stem).read_text())
  fm,sm=full['checkpoint']['metadata'],small['checkpoint']['metadata'];assert fm['round']==sm['round']
  n,p,lens,rows=parse_input(Path(full['checkpoint']['path']))
  nn,pp,slens,srows=parse_input(Path(small['checkpoint']['path']));bm=fm['original_generators']
  assert fm['omitted_basis_rows']==0 and fm['omitted_basis_terms']==0
  available=rows[bm:]
  # Full export is already in degree/length/index order. Stable greedy filtering
  # therefore preserves the original tie-break order without inferring indices.
  priority=[(sum(next(iter(row))),len(row)) for row in available]
  assert priority==sorted(priority)
  selected=[];used=0
  for row in available:
   if len(row)<=2-used and len(selected)+bm<100000:selected.append(row);used+=len(row)
  assert srows[bm:]==selected
  assert sm['available_basis_rows']==len(available)
  assert sm['available_basis_terms']==sum(map(len,available))
  print('PASS exact budget2 selection',name,prime,len(selected),sm['omitted_basis_rows'],flush=True)
print('PASS',totals,flush=True)
