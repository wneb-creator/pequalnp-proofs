from pathlib import Path
import itertools,json
import sympy as S
b=Path(__file__).parent;beta,gamma=S.symbols('beta gamma');loc={'beta':beta,'gamma':gamma}
d0=json.loads((b/'c4-nonzero-bivariate-0.json').read_text());d1=json.loads((b/'c4-nonzero-bivariate-1.json').read_text())
results=[]
for swapped in(False,True):
 for sb,sg in itertools.product((-1,1),repeat=2):
  mapping={beta:sb*(gamma if swapped else beta),gamma:sg*(beta if swapped else gamma)}
  item={'swapped':swapped,'beta_sign':sb,'gamma_sign':sg,'branches':{}}
  for branch in('v_zero','v_nonzero'):
   p0=[S.Poly(S.sympify(e,locals=loc).subs(mapping,simultaneous=True),beta,gamma,domain=S.QQ)for e in d0['branches'][branch]];p1=[S.Poly(S.sympify(e,locals=loc),beta,gamma,domain=S.QQ)for e in d1['branches'][branch]]
   matched=[]
   for p in p0:
    found=[]
    for j,q in enumerate(p1):
     c=p.LC()/q.LC()
     if p==q.mul_ground(c):found.append([j,str(c)])
    matched.append(found)
   item['branches'][branch]=matched
  if all(all(x for x in m)for m in item['branches'].values()):results.append(item)
print(json.dumps({'exact_signed_permutation_matches':results},indent=2));(b/'c4_case_symmetry.json').write_text(json.dumps(results,indent=2)+'\n')
