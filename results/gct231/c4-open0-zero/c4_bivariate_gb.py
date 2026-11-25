from pathlib import Path
import argparse,json,time
import sympy as S
p=argparse.ArgumentParser();p.add_argument('case',type=int);p.add_argument('branch');p.add_argument('--saturate',action='store_true');args=p.parse_args()
b=Path(__file__).parent;src=b/('c4-nonzero-bivariate-'+str(args.case)+'.json');data=json.loads(src.read_text());beta,gamma,t=S.symbols('beta gamma t');loc={'beta':beta,'gamma':gamma};eq=[S.sympify(s,locals=loc)for s in data['branches'][args.branch]]
# A product is zero exactly when its squarefree part is zero over the complex numbers.
eq=[S.Poly(e,beta,gamma,domain=S.QQ).sqf_part().as_expr() if e!=0 else e for e in eq]
vars=(beta,gamma)
if args.saturate:
 eq.append(t*S.sympify(data['saturation_nonzero'],locals=loc)-1);vars=(t,beta,gamma)
start=time.monotonic();G=S.groebner(eq,*vars,order='grevlex',domain=S.QQ,method='buchberger')
result={'case':args.case,'branch':args.branch,'saturated':args.saturate,'equations':list(map(str,eq)),'basis':list(map(str,G.polys)),'unit':len(G.polys)==1 and G.polys[0].as_expr()==1,'seconds':time.monotonic()-start,'scope':'Exact rational CAS result for necessary branch equations; not yet a Lean certificate or whole-gap result.'}
name='c4-bivariate-'+str(args.case)+'-'+args.branch+('-sat'if args.saturate else '')
(b/(name+'.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
