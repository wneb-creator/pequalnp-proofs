import itertools,json,sympy as s
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
lam=s.Symbol('lam');records=[]
for case in [2,3]:
 d=json.loads((base/f'c4-nonzero-square-{case}.json').read_text());vs=s.symbols(' '.join(d['variables']));loc=dict(zip(d['variables'],vs))
 for sign in [1,-1]:
  vals=([-2*sign,sign,s.Rational(-1,2),0,6*sign] if case==2 else [2*sign,s.Rational(1,2),sign,0,-6*sign])
  sub=dict(zip(vs,vals));eq=[s.factor(s.sympify(t,locals=loc).subs(sub)) for t in d['equations']]
  assert eq==[0,0,0,0,-1,0,0]
  G=s.Matrix([[s.sympify(t,locals=loc).subs(sub) for t in row] for row in d['gram_W']]);R=s.Matrix([[s.sympify(t,locals=loc).subs(sub) for t in row] for row in d['gram_R']])
  determinant=s.factor((R-lam*G).det());assert determinant==lam**3*(13*lam-4)/4
  record={'case':case,'sign':sign,'lift':list(map(str,vals)),'equation_values':list(map(str,eq)),'determinant':str(determinant)}
  records.append(record);print(json.dumps(record),flush=True)
(base/'c4-reduced-root-obstruction.json').write_text(json.dumps(records,indent=2))
print('ALL_FOUR_LIFTS_FAIL_OMITTED_SQUARE_CONDITION',flush=True)
