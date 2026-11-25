from pathlib import Path
import json,resource
import sympy as S
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
out=Path(__file__).parent;data=json.loads((out/'axis-five.json').read_text())
loc={n:S.Symbol(n) for n in data['unknowns']};u=loc['u'];b=loc['o1'];d=loc['o5'];h=u*u-2
cases={'equal':b,'different':(u-5*b)/(u*b-5)}
for name,replacement in cases.items():
 rows=[]
 for record in data['equations']:
  f=S.sympify(record['coefficient'],locals=loc)
  value=S.together(f.subs(d,replacement));num,den=S.fraction(value)
  value=S.factor(S.rem(S.expand(num),h,u)) if record['source_index'] is not None else h
  if value==0:continue
  variables=[loc[n] for n in ['o7','o8','o1','u']]
  content,primitive=S.Poly(value,*variables,domain=S.QQ).primitive()
  value=S.factor(primitive.as_expr())
  rows.append({'source_index':record['source_index'],'coefficient':str(value),'denominator':str(S.factor(den)),'content':str(content)})
  print(name,record['source_index'],'terms',len(primitive.terms()),'degree',primitive.total_degree(),flush=True)
 result={'unknowns':['o7','o8','o1','u'],'equations':rows,'substitution':{'o5':str(replacement)},'case':name,'scope':'Necessary axis-five branch from (o1-o5)*(u*o1*o5+5*o1-5*o5-u)=0. Different branch divisor u*o1-5 is nonzero since u^2=2; no new normalization.'}
 (out/('axis-four-'+name+'.json')).write_text(json.dumps(result,indent=2)+'\n')
