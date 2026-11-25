from pathlib import Path
import sympy as S
from verify_certificate import input_polynomials
base=Path(__file__).resolve().parents[1]
for case in (0,1):
    for branch in ('v_zero','v_nonzero'):
        stem=base/'c4-small-certificates'/f'case{case}-{branch}'
        raw=stem.with_suffix('.f4.in').read_text().splitlines()
        char,n,m=map(int,raw[0].split());names=raw[1].split();xs=S.symbols(names)
        assert char==0 and len(names)==n
        original=[]
        for line in raw[2:]:
            poly=S.Poly(S.sympify(line,locals=dict(zip(names,xs))),*xs,domain=S.QQ)
            original.append({exps:coef for exps,coef in poly.terms()})
        renamed,run=input_polynomials(Path(str(stem)+'-run.f4.in'))
        assert len(run)==m and run==original
        print('PASS exact original-to-trace input mapping',case,branch,n,m,flush=True)
