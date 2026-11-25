from pathlib import Path
import json
import resource
import time
import sympy as S

resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(45,50))
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
data=json.loads((base/'trace-Bone-systems.json').read_text())['cases']['same-index']
names={name:S.Symbol(name) for name in data['variables']}
equations=[S.sympify(g,locals=names) for g in data['generators']]
xs=[names[k] for k in ['p1','p3','p5']]
kernel=[S.expand(equations[i].subs({names['d1']:1,names['d3']:1}))
        for i in [2,6,11]]
es=S.symbols('E1 E2 E3')
symmetric=[]
for g in kernel:
    expression,remainder,mapping=S.symmetrize(g,xs,formal=True,symbols=es)
    assert remainder==0
    assert S.expand(expression.subs(dict(mapping),simultaneous=True)-g)==0
    symmetric.append(expression)
e2sol=S.solve(symmetric[0],es[1])[0]
e3sol=S.solve(symmetric[1],es[2])[0]
last=S.factor(symmetric[2].subs({es[1]:e2sol,es[2]:e3sol},simultaneous=True))
sums=S.solve(last,es[0])
x=S.Symbol('x')
branches=[]
for value in sums:
    ev=[value,S.expand(e2sol.subs(es[0],value)),S.expand(e3sol.subs(es[0],value))]
    f=S.Poly(x**3-ev[0]*x**2+ev[1]*x-ev[2],x)
    _,primitive=f.clear_denoms()
    branches.append({'elementary_symmetric_values':list(map(str,ev)),
                     'root_polynomial':str(primitive.as_expr()),
                     'discriminant':str(S.discriminant(primitive.as_expr(),x)),
                     'irreducible_over_QQ':bool(primitive.is_irreducible)})
report={'status':'PASS','scope':'Exact classification of B=0 kernel directions '
                'with D_i squared all equal and nonzero, normalized to D=(1,1,1). '
                'No companion nonextension conclusion.',
        'symmetric_kernel_generators':list(map(str,symmetric)),
        'solved_E2':str(e2sol),'solved_E3':str(e3sol),
        'last_equation':str(last),'branches':branches,
        'seconds':time.monotonic()-start}
(base/'trace-Bone-equal-D.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2),flush=True)
