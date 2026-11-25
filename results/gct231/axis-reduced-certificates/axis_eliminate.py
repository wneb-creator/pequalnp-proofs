from pathlib import Path
import json,resource
import sympy as S
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
out=Path(__file__).parent;data=json.loads((out/'axis-cubic-shift.json').read_text())
loc={n:S.Symbol(n) for n in data['unknowns']};u=loc['u'];b=loc['o1'];d=loc['o5'];h=u*u-2
polys={r['source_index']:S.sympify(r['coefficient'],locals=loc) for r in data['equations']}
assert S.expand(polys[8].subs(b,1))==4*u-20
assert S.expand(polys[12].subs(d,1))==-4*u-20
sub={}
for index,var in [(8,loc['d7']),(12,loc['d8'])]:
 solution=S.solve(polys[index],var)[0]
 solution=S.cancel(solution*u/u)
 numerator,denominator=S.fraction(solution)
 # Reduce the reciprocal u using u^2=2, retaining only b-1 or d-1 denominators.
 numerator=S.rem(S.expand(numerator*u),h,u)
 denominator=S.rem(S.expand(denominator*u),h,u)
 solution=S.cancel(numerator/denominator)
 sub[var]=solution
 print('SOLVE',var,solution,flush=True)
 check=S.together(polys[index].subs(var,solution));num,den=S.fraction(check)
 assert S.rem(S.expand(num),h,u)==0
rows=[]
for record in data['equations']:
 f=S.sympify(record['coefficient'],locals=loc)
 value=S.together(f.subs(sub,simultaneous=True));num,den=S.fraction(value)
 reduced=S.factor(S.rem(S.expand(num),h,u)) if record['source_index'] is not None else h
 if reduced==0:continue
 variables=[loc[n] for n in ['o7','o8','o1','o5','u']]
 content,primitive=S.Poly(reduced,*variables,domain=S.QQ).primitive();reduced=S.factor(primitive.as_expr())
 rows.append({'source_index':record['source_index'],'coefficient':str(reduced),'denominator':str(S.factor(den)),'content':str(content)})
 print('ROW',record['source_index'],'terms',len(primitive.terms()),'degree',primitive.total_degree(),flush=True)
result={'unknowns':['o7','o8','o1','o5','u'],'equations':rows,'substitution':{str(k):str(v) for k,v in sub.items()},'nonzero_assumptions':['o1-1','o5-1'],'boundary_certificates':['u^2=2 and o1=1 force u=5, contradiction','u^2=2 and o5=1 force u=-5, contradiction'],'scope':'Necessary axis-kernel system after exact invertible shift and solving two linear cubic equations; denominator conditions separately forced by source equations.'}
(out/'axis-five.json').write_text(json.dumps(result,indent=2)+'\n')
