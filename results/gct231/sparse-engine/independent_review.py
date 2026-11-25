"""Independent frozen patch/provenance checks and small exact engine controls."""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import sympy as s


base=Path(__file__).resolve().parent
out=base/'independent-review'
out.mkdir(exist_ok=True)
print('Review start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
provenance=json.loads((base/'provenance.json').read_text())
def check_hashes():
    for name,expected in provenance['files'].items():
        assert hashlib.sha256((base/name).read_bytes()).hexdigest()==expected,name
check_hashes()
print('All17 frozen source/library/binary/control hashes verified',flush=True)
assert (base/'qqfix/gb.c').read_bytes()==(base/'msolve/src/neogb/gb.c').read_bytes()
orig=(base/'msolve/src/neogb/la_qq.c').read_text()
patched=orig
for old,new in [
 ('    exact_sparse_reduced_echelon_form_ab_first_qq(mat, bs, st);',
  '    exact_sparse_reduced_echelon_form_ab_first_qq(mat, bs, st);\n    st->np = mat->np;'),
 ('    exact_sparse_reduced_echelon_form_qq(mat, bs, st);',
  '    exact_sparse_reduced_echelon_form_qq(mat, bs, st);\n    st->np = mat->np;'),
 ('    mat->np = nrows;', '    st->np = mat->np = nrows;')]:
    assert patched.count(old)==1
    patched=patched.replace(old,new)
assert patched==(base/'qqfix/la_qq.c').read_text()
print('Patched core differs only by the three stated pivot-count assignments',flush=True)
dynamic=subprocess.check_output(['readelf','-d',str(base/'neogb_cli_qqfix')],text=True)
(out/'dynamic.txt').write_text(dynamic)
assert '[libneogb_qqfix.so]' in dynamic and '['+str(base)+']' in dynamic
print('Patched binary links the expected library using the recorded runpath',flush=True)

records=[]
def run_case(name,infile,pairs):
    data=list(map(int,infile.read_text().split()))
    n,m,p,terms=data[:4];lengths=data[4:4+m];pos=4+m
    variables=s.symbols('x:'+str(n))
    polys=[]
    for length in lengths:
        expr=0;seen=set()
        for _ in range(length):
            num,den=data[pos:pos+2];pos+=2
            powers=tuple(data[pos:pos+n]);pos+=n
            assert powers not in seen
            seen.add(powers)
            expr+=s.Rational(num,den)*s.prod(v**e for v,e in zip(variables,powers))
        polys.append(expr)
    assert pos==len(data) and sum(lengths)==terms
    prefix=out/name;basisfile=out/(name+'.basis.json')
    cmd=[sys.executable,str(base/'run_neogb_qqfix.py'),str(infile),str(basisfile),str(prefix),
         '--seconds','20','--memory-mib','512','--pairs',str(pairs)]
    result=subprocess.run(cmd,capture_output=True,text=True,timeout=30)
    prefix.with_suffix('.runner.log').write_text(result.stdout+result.stderr)
    assert result.returncode==0,(name,result.stderr)
    meta=json.loads(prefix.with_suffix('.result.json').read_text())
    assert meta['status']=='COMPLETED',meta
    exported=json.loads(basisfile.read_text())
    assert exported['characteristic']==p and exported['nvars']==n
    assert sum(map(len,exported['basis']))==exported['nterms']
    actual=[sum(s.Integer(c)*s.prod(v**e for v,e in zip(variables,powers)) for c,powers in poly)
            for poly in exported['basis']]
    kwargs={'modulus':p} if p else {'domain':s.QQ}
    expected=s.groebner(polys,*variables,order='grevlex',**kwargs)
    normalize=lambda f:tuple(s.Poly(f,*variables,**kwargs).monic().terms())
    assert {normalize(f) for f in actual}=={normalize(f.as_expr()) for f in expected.polys}
    expected_unit=list(expected)==[1]
    assert meta['unit_basis']==expected_unit
    records.append({'name':name,'characteristic':p,'pairs_per_round':pairs,'basis_size':len(actual),'unit':expected_unit})
    print(name,'PASS','basis_size',len(actual),'unit',expected_unit,flush=True)

for p in (0,1009):
    for name in ('unit','nonunit','rational'):
        run_case('frozen-'+name+'-p'+str(p),base/('qqfix-sanity-'+name+'-p'+str(p)+'.in'),0)

x,y,z=s.symbols('x y z')
extra={
 'threevar-rational':[x*y-1,y*z-1,z*z-2],
 'threevar-unit':[x*y-1,y*z-1,x*z-1,x+y+z],
 'redundant-zero-reductions':[x*x-y,y*y-z,z*z-1,x*x-y]}
for name,polys in extra.items():
    terms=[s.Poly(f,x,y,z,domain=s.QQ).terms() for f in polys]
    text=f'3 {len(terms)} 0 {sum(map(len,terms))}\n'+' '.join(map(str,map(len,terms)))+'\n'
    for poly in terms:
        for powers,c in poly:
            num,den=c.as_numer_denom()
            text+=f'{num} {den} '+' '.join(map(str,powers))+'\n'
    infile=out/(name+'.in');infile.write_text(text)
    run_case(name,infile,1)
check_hashes()
(out/'results.json').write_text(json.dumps(records,indent=2)+'\n')
print('All9 independent QQ/FF reduced-basis comparisons passed; frozen hashes unchanged',flush=True)
print('Scope: tested research engine, not an ideal-membership certificate or Lean proof',flush=True)
print('Review finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
