"""Read-only audit of frozen checkpoint source, controls, and grouped input."""
from pathlib import Path
import hashlib,json,difflib
import sympy as S
root=Path(__file__).resolve().parents[1]; base=root/'sparse-engine'; dest=Path(__file__).parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
prov=json.loads((base/'checkpoint/provenance.json').read_text())
for name,h in prov['files'].items(): assert digest(base/name)==h,name
print('PASS all',len(prov['files']),'frozen provenance hashes',flush=True)

# Confirm every core modification at reviewed injection sites and nowhere else.
old=(base/'msolve/src/neogb/f4.c').read_text(); expected=old
replacements=[
 ('    done = initialize_f4(&bs, &md, &mat, gmd, gbs, fc);',
  '    done = initialize_f4(&bs, &md, &mat, gmd, gbs, fc);\n    uint64_t pnp_round = 0;\n    pnp_checkpoint_snapshot(bs,md,pnp_round,1);'),
 ('        print_round_timings(VERBSTREAM, md, rrt, crt);',
  '        print_round_timings(VERBSTREAM, md, rrt, crt);\n        if (*errp == 0) pnp_checkpoint_snapshot(bs,md,++pnp_round,0);'),
 ('        reduce_final_basis(bs, mat, md);',
  '        reduce_final_basis(bs, mat, md);\n        pnp_checkpoint_snapshot(bs,md,pnp_round,1);')]
for a,b in replacements:
    assert expected.count(a)==1
    expected=expected.replace(a,b)
assert expected==(base/'checkpoint/engine/f4.c').read_text()
assert (base/'checkpoint/engine/gb.c').read_text()==(base/'native/engine/gb.c').read_text().replace('#include "f4.c"','#include "checkpoint_basis.c"\n#include "f4.c"')
for name in ['la_qq.c','convert.c']:
    assert (base/f'checkpoint/engine/{name}').read_bytes()==(base/f'native/engine/{name}').read_bytes()
assert (base/'checkpoint/engine/checkpoint_basis.c').read_bytes()==(base/'checkpoint_basis.c').read_bytes()
(dest/'wrapper-diff.txt').write_text(''.join(difflib.unified_diff((base/'native/neogb_cli_native.c').read_text().splitlines(True),(base/'checkpoint/neogb_cli_checkpoint.c').read_text().splitlines(True))))
print('PASS core modifications exactly four snapshot/include hooks; arithmetic core unchanged',flush=True)

def parse_input(p):
    lines=p.read_text().splitlines();n,m,char,terms=map(int,lines[0].split());lengths=list(map(int,lines[1].split()))
    assert len(lengths)==m and min(lengths)>0 and sum(lengths)==terms and len(lines)==terms+2
    pos=2; tables=[]
    for size in lengths:
        table={}
        for line in lines[pos:pos+size]:
            num,den,*exps=map(int,line.split());assert len(exps)==n and min(exps)>=0 and den>0
            assert tuple(exps) not in table
            coef=num*pow(den,-1,char)%char;assert coef
            table[tuple(exps)]=coef
        tables.append(table);pos+=size
    return n,char,lengths,tables
def polynomials(tables,n,p):
    xs=S.symbols('x:'+str(n))
    return xs,[S.Poly.from_dict(t,xs,modulus=p) for t in tables]
def canonical(polys):return sorted(tuple(sorted(poly.monic().terms())) for poly in polys if not poly.is_zero)

controls=base/'checkpoint/controls-v2'; totals={'snapshots':0,'rows':0,'bases':0}
for name in ['unit','nonunit','rational']:
  for prime in [101,1009,65537]:
    input_path=controls/f'{name}-p{prime}.in';n,p,lens,tables=parse_input(input_path)
    xs,polys=polynomials(tables,n,p);ideal=S.groebner([x.as_expr() for x in polys],*xs,modulus=p,order='grevlex')
    for mode in ['full','stop1','resumed']:
      stem=f'{name}-p{prime}-{mode}';result=json.loads((controls/(stem+'.result.json')).read_text())
      assert result['base_input_sha256']==digest(input_path)
      assert result['binary_sha256']==prov['files']['checkpoint/neogb_cli_checkpoint']
      assert result['library_sha256']==prov['files']['checkpoint/libneogb_checkpoint.so']
      assert result['input_sha256']==digest(Path(result['command'][1]))
      assert result['status'] in (['COMPLETED','STOPPED_AFTER_CHECKPOINT'] if mode=='stop1' else ['COMPLETED'])
      snapshots=sorted(controls.glob(stem+'.checkpoint.s*.in'));assert 1<=len(snapshots)<=2
      for snapshot in snapshots:
        nn,pp,ll,tt=parse_input(snapshot);assert (nn,pp)==(n,p) and ll[:len(lens)]==lens and tt[:len(tables)]==tables
        _,extra=polynomials(tt[len(tables):],n,p)
        for poly in extra:assert ideal.reduce(poly.as_expr())[1]==0
        totals['snapshots']+=1;totals['rows']+=len(extra)
      if result['status']=='COMPLETED':
        out=controls/(stem+'.basis.json');data=json.loads(out.read_text());assert (data['nvars'],data['characteristic'])==(n,p)
        ts=[]
        for poly in data['basis']:
          td={}
          for coef,exps in poly:
            assert len(exps)==n and tuple(exps) not in td
            td[tuple(exps)]=int(coef)%p
          ts.append(td)
        assert sum(map(len,ts))==data['nterms']
        _,actual=polynomials(ts,n,p);assert canonical(actual)==canonical(ideal.polys)
        assert result['output_sha256']==digest(out)
        totals['bases']+=1
    print('PASS CONTROL',name,prime,flush=True)
assert not (controls/'bad-prefix.log').exists()
badlog=(controls/'bad-prefix.driver.log').read_text()
assert 'AssertionError' in badlog and 'bnum*pow' in badlog
print('PASS independent all retained control snapshots/results',totals,flush=True)

original=json.loads((root/'star-full-generate-equations.json').read_text())
grouped=json.loads((root/'star-full-grouped-equations.json').read_text())
assert grouped['reordered_from_sha256']==digest(root/'star-full-generate-equations.json')
old=original['unknowns'];new=grouped['unknowns'];assert len(new)==len(old)==18 and set(new)==set(old)
for key,value in original.items():
    if key not in ('unknowns','scope'):assert grouped[key]==value,key
assert new==['d0','d3','d6','o0','o3','o6','d1','d4','d7','o1','o4','o7','d2','d5','d8','o2','o5','o8']
n,p,lens,tables=parse_input(root/'neogb-star-full-grouped-p1009.in');assert (n,p,len(lens))==(18,1009,31)
symbols=S.symbols(new);locals=dict(zip(new,symbols));term_count=0
for i,(record,actual) in enumerate(zip(original['equations'],tables)):
    poly=S.Poly(S.sympify(record['coefficient'],locals=locals),*symbols,domain=S.QQ)
    content,primitive=poly.clear_denoms()[1].primitive()
    assert content!=0 and int(content)%p!=0
    expected={exps:int(coef)%p for exps,coef in primitive.terms() if int(coef)%p}
    assert expected==actual,i
    term_count+=len(expected)
print('PASS grouped full31 source unchanged, exact 18-variable permutation and all',term_count,'modular terms',flush=True)
print('PASS independent review checks.',flush=True)
