import sympy as s,json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-75/gct231')
o=s.symbols('o:9')
cases=[('path-central','path',[0,2,3,5,6,8],None),('path-c4','path',[0,1,2,6,7,8],None),('triangle-star-dependent','triangle',[2,4,6],o[0]*o[5]*o[7]+o[1]*o[3]*o[8])]
for name,source,zero,extra in cases:
 data=json.loads((base/(source+'-full-f5b-equations.json')).read_text())
 sub={o[i]:0 for i in zero}
 out={k:v for k,v in data.items() if k not in ['unknowns','matrix','equations']}
 out['unknowns']=[x for x in data['unknowns'] if s.Symbol(x) not in sub]
 out['matrix']=[[str(s.expand(s.sympify(x).subs(sub))) for x in row] for row in data['matrix']]
 out['equations']=[]
 for row in data['equations']:
  cc=s.expand(s.sympify(row['coefficient']).subs(sub))
  if cc!=0:out['equations'].append({'monomial':row['monomial'],'coefficient':str(cc)})
 if extra is not None:out['equations'].append({'monomial':None,'coefficient':str(extra),'kind':'additional star determinant'})
 out['scope']='Conditional matroid stratum, not a full chart exclusion'
 out['zero_parameters']=[str(x) for x in sub]
 path=base/'fresh'/(name+'-equations.json');path.write_text(json.dumps(out,indent=2))
 vs=s.symbols(' '.join(out['unknowns']));counts=[len(s.Poly(s.sympify(q['coefficient']),*vs).terms()) for q in out['equations']]
 print(name,'variables',len(vs),'equations',len(out['equations']),'terms',sum(counts),'path',path,flush=True)
