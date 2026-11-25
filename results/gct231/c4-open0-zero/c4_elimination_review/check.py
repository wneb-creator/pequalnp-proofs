"""Independent exact arithmetic audit; no Gröbner engine or source imports."""
from pathlib import Path
import json, hashlib
import sympy as S

base = Path(__file__).resolve().parents[1]
a,b,g,u,v = S.symbols('alpha beta gamma u v')
variables = (b,g,u,v)
local = {str(x):x for x in (a,b,g,u,v)}
hashes = {}
def read(name):
    p = base / name
    hashes[name] = hashlib.sha256(p.read_bytes()).hexdigest()
    return json.loads(p.read_text())
def expr(x): return S.sympify(x, locals=local)
def equal(x,y): return S.cancel(x-y)==0
def ratio_supported(original, result, saturation, label):
    if original == 0:
        assert result == 0, label
        return
    assert result != 0, label
    ratio = S.cancel(original/result)
    num, den = ratio.as_numer_denom()
    factors = []
    for side in (num,den):
        constant, facs = S.factor_list(side, *variables)
        assert constant != 0, label
        for factor, multiplicity in facs:
            assert not factor.has(u,v), (label, factor)
            assert S.rem(saturation, factor, b,g) == 0, (label, factor)
            factors.append((str(factor), multiplicity))
    print('SCALING',label,str(ratio),flush=True)
def linear_resultant(linear, polynomial):
    # det Sylvester(a*u+b,P): sum P_j*(-b)^j*a^(n-j).
    pl = S.Poly(linear,u); pp = S.Poly(polynomial,u)
    assert pl.degree() == 1
    ac,bc = pl.all_coeffs(); n = pp.degree()
    return S.expand(sum(pp.nth(j)*(-bc)**j*ac**(n-j) for j in range(n+1)))

for case in (0,1):
    source = read(f'fresh/c4-nonzero-square-{case}.json')
    output = read(f'c4-nonzero-bivariate-{case}.json')
    raw = dict(zip(source['equation_labels'],map(expr,source['equations'])))
    assert len(raw)==len(source['equation_labels'])==7
    assert equal(raw['product_scales'],a*b*g-1)
    sub = {k:S.cancel(p.subs(a,1/(b*g))) for k,p in raw.items()}
    sat = expr(output['saturation_nonzero'])
    determinant = expr(source['det_W']).subs(a,1/(b*g))
    expected_sat=3*b*g*(2*b*b*g*g-1)*(b*b+b-1)
    assert equal(sat,expected_sat)
    assert equal(determinant,3*(2*b*b*g*g-1)*(b*b+b-1)/(2*b*b*g*g))
    pol = {k:expr(x) for k,x in output['equations_before_resultants'].items()}
    F,R,L,Q0,Q2,C0,C2,H = [pol[k] for k in ('F','R','L','Q0','Q2','C0','C2','H')]
    assert not F.has(u,v)
    assert all(not x.has(v) for x in (R,L,Q0,Q2,C0,C2,H))
    ratio_supported(sub['normal_q'],F,sat,f'{case}:normal_q')
    ratio_supported(sub['normal_R'],R,sat,f'{case}:normal_R')
    ratio_supported(sub['normal_L'],v*L,sat,f'{case}:normal_L=v*L')
    ratio_supported(sub['q_w'],Q0+Q2*v*v,sat,f'{case}:q_w')
    ratio_supported(sub['c_w'],C0+C2*v*v,sat,f'{case}:c_w')
    hratio=S.cancel((Q2*C0-C2*Q0)/H)
    assert hratio.is_Rational and hratio != 0
    print('H_SCALE',case,str(hratio),flush=True)
    assert S.degree(R,u)==S.degree(L,u)==1
    assert S.degree(Q0,u)==S.degree(C0,u)==2 and S.degree(H,u)==3
    assert S.Poly(Q0,u).nth(1)==S.Poly(C0,u).nth(1)==0
    # Res(A*u^2+B,C*u^2+D)=(A*D-B*C)^2; no denominator.
    qq,cc=S.Poly(Q0,u),S.Poly(C0,u)
    res_qc=S.expand((qq.nth(2)*cc.nth(0)-qq.nth(0)*cc.nth(2))**2)
    expected={
      'v_zero':[F,linear_resultant(R,Q0),linear_resultant(R,C0),res_qc],
      'v_nonzero':[F,linear_resultant(R,L),linear_resultant(R,H),linear_resultant(L,H)]}
    for branch in ('v_zero','v_nonzero'):
        rows=list(map(expr,output['branches'][branch]))
        assert len(rows)==4
        for i,(original,result) in enumerate(zip(expected[branch],rows)):
            ratio_supported(original,result,sat,f'{case}:{branch}:{i}')
        # Parse the actual flat certificate input independently.
        stem=base/'c4-small-certificates'/f'case{case}-{branch}'
        flat=stem.with_suffix('.f4.in').read_text().splitlines()
        hashes[str(stem.relative_to(base))+'.f4.in']=hashlib.sha256(stem.with_suffix('.f4.in').read_bytes()).hexdigest()
        char,n,nrows=map(int,flat[0].split()); assert char==0
        names=flat[1].split(); assert len(names)==n
        syms=S.symbols(' '.join(names)); syms=(syms,) if n==1 else syms
        actual=[S.sympify(t,locals=dict(zip(names,syms))) for t in flat[2:] if t.strip()]
        wanted=rows+([S.Symbol('inverse_det')*sat-1] if branch=='v_nonzero' else [])
        assert len(actual)==nrows==len(wanted)
        assert all(equal(x,y) for x,y in zip(actual,wanted))
        sparse=stem.with_suffix('.sparse.in').read_text().splitlines()
        hashes[str(stem.relative_to(base))+'.sparse.in']=hashlib.sha256(stem.with_suffix('.sparse.in').read_bytes()).hexdigest()
        nn,nr,ch,nt=map(int,sparse[0].split());counts=list(map(int,sparse[1].split()))
        assert (nn,nr,ch)==(n,nrows,0) and sum(counts)==nt and len(counts)==nr
        assert len(sparse)==nt+2
        pos=2
        for expected_poly,count in zip(actual,counts):
            actual_poly=0; seen=set()
            for line in sparse[pos:pos+count]:
                ints=list(map(int,line.split())); numerator,denominator,*powers=ints
                assert denominator>0 and len(powers)==n and min(powers)>=0
                assert tuple(powers) not in seen;seen.add(tuple(powers))
                actual_poly+=S.Rational(numerator,denominator)*S.prod(x**k for x,k in zip(syms,powers))
            assert equal(actual_poly,expected_poly)
            pos+=count
        print('INPUT_PASS',case,branch,n,nrows,nt,flush=True)
    print('CASE_PASS',case,flush=True)

(Path(__file__).parent/'checked-source-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
print('PASS: exact factors, polynomial-resultant identities and four unreduced certificate input systems.',flush=True)
