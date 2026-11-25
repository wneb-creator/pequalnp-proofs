from pathlib import Path
import json,resource,time
import sympy as S
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
out=Path(__file__).parent;data=json.loads((out/'axis_x.json').read_text())
loc={n:S.Symbol(n) for n in data['unknowns']}
p=loc['d0'];b=loc['o1'];d=loc['o5'];h=p*p+2*p-1
sub={loc['d1']:2*(p-1)*(b+1),loc['d5']:-2*(p+3)*(d+1)}
rows=[]
for old in data['equations']:
 original=S.sympify(old['coefficient'],locals=loc)
 reduced=S.factor(S.rem(S.expand(original.subs(sub,simultaneous=True)),h,p))
 if reduced!=0:
  content,primitive=S.Poly(reduced,*sorted(reduced.free_symbols,key=str),domain=S.QQ).primitive()
  reduced=S.factor(primitive.as_expr())
  rows.append({'source_index':old['source_index'],'coefficient':str(reduced)})
  print(old['source_index'],reduced,flush=True)
rows.append({'source_index':None,'coefficient':str(h)})
names=[n for n in data['unknowns'] if n not in ['d1','d5']]
result={'unknowns':names,'equations':rows,'substitution':{str(k):str(v) for k,v in sub.items()},'relation':str(h),'scope':'Axis-kernel necessary system; d1,d5 elimination uses only h=p^2+2p-1 and the two mixed quadratic equations; all substitution denominators have polynomial inverses modulo h.'}
(out/'axis-seven.json').write_text(json.dumps(result,indent=2)+'\n')
print('EXPORT',len(names),len(rows),flush=True)
