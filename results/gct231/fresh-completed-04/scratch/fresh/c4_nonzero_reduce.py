import json,sympy as s
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
alpha,beta,gamma,u,v=s.symbols('alpha beta gamma u v')
P,B,A,U,V,sat=s.symbols('P B A U V sat')
loc={str(t):t for t in [alpha,beta,gamma,u,v]}
for index in [2,3]:
    d=json.loads((base/f'c4-nonzero-square-{index}.json').read_text())
    if index==2:
        sub={alpha:P/beta,gamma:1/P,u:U,v:V/beta};power=beta;newpower=B;other=[P,U,V];newvs=[P,B,U,V]
    else:
        sub={gamma:1/(alpha*beta),u:U,v:V/alpha};power=alpha;newpower=A;other=[beta,U,V];newvs=[A,beta,U,V]
    def convert(expr):
        num,den=s.together(s.sympify(expr,locals=loc).subs(sub,simultaneous=True)).as_numer_denom()
        pol=s.Poly(s.expand(num),power)
        assert all(m[0]%2==0 for m,c in pol.terms())
        result=s.factor(sum(c*newpower**(m[0]//2) for m,c in pol.terms()))
        return result,str(den)
    equations=[];denoms=[]
    for i in [1,2,3,5,6]:
        n,den=convert(d['equations'][i]);equations.append(n);denoms.append(den)
    detW,detden=convert(d['det_W'])
    nonzero=(P*B if index==2 else A*beta)*detW
    equations.append(sat*nonzero-1)
    out={'variables':list(map(str,newvs+[sat])),'equations':list(map(str,equations)),
         'original_case':index,'substitution':{str(k):str(t) for k,t in sub.items()},
         'squared_variable':{str(power)+'**2':str(newpower)},'discarded_denominators':denoms,
         'det_W_numerator':str(detW),'det_W_denominator':detden,
         'scope':'Necessary saturated equations for nonzero-product C4 branch with nondegenerate W4. No verdict; determinant-square equation intentionally omitted.'}
    target=base/f'c4-nonzero-reduced-{index}.json';target.write_text(json.dumps(out,indent=2))
    print('CASE',index,'VARS',out['variables'],'TERM_COUNTS',[len(s.Poly(t,*newvs,sat).terms()) for t in equations], 'DEGREES',[s.Poly(t,*newvs,sat).total_degree() for t in equations], 'DET',detW,flush=True)
