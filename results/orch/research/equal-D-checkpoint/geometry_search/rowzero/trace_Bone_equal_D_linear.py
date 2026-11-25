from pathlib import Path
import json
import resource
import sys
import time
import sympy as S

resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(45,50))
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
data=json.loads((base/'trace-Bone-systems.json').read_text())['cases']['same-index']
names={name:S.Symbol(name) for name in data['variables']}
gens=[S.sympify(g,locals=names) for g in data['generators']]
x,y,u,v,tau=S.symbols('x y u v tau')
which=int(sys.argv[1]) if len(sys.argv)>1 else 7
s=-S.Rational(which,2)
e2=s*s/2+3*s+9;e3=2*s+6
f=x**3-s*x*x+e2*x-e3
g=y*y+(x-s)*y+x*x-s*x+e2

def red(a):
    return S.expand(S.rem(S.rem(S.expand(a),g,y),f,x))

basis=[x**i*y**j for j in range(2) for i in range(3)]
def inverse(a):
    columns=[]
    for b in basis:
        p=S.Poly(red(a*b),x,y)
        columns.append([p.coeff_monomial(c) for c in basis])
    M=S.Matrix.hstack(*(S.Matrix(c) for c in columns))
    values=M.inv()*S.Matrix([1,0,0,0,0,0])
    ans=sum(v*b for v,b in zip(values,basis))
    assert red(a*ans)==1
    return ans

sub={names['d1']:1,names['d3']:1,names['p1']:x,
     names['p3']:y,names['p5']:s-x-y,
     names['d0']:u,names['d2']:v,names['tau']:tau}
eq=[red(h.subs(sub,simultaneous=True)) for h in gens]
unknowns=[names[k] for k in ['p0','p2','p4']]
indices=[1,5,10]
M,rhs=S.linear_eq_to_matrix([eq[i] for i in indices],unknowns)
det=red(M.det())
det_inv=inverse(det)
Minv=M.adjugate().applyfunc(lambda a:red(a*det_inv))
assert (M*Minv-S.eye(3)).applyfunc(red)==S.zeros(3)
sol=(Minv*rhs).applyfunc(red)
sub.update(dict(zip(unknowns,sol)))
powers={name:[S.Integer(1)] for name in names.values()}
for name in names.values():
    for degree in range(1,5):
        powers[name].append(red(powers[name][-1]*sub[name]))
residuals=[]
for h in gens:
    result=0
    for monomial,coefficient in S.Poly(h,*names.values()).terms():
        term=coefficient
        for name,degree in zip(names.values(),monomial):
            if degree:term=red(term*powers[name][degree])
        result+=term
    residuals.append(red(result))
assert all(residuals[i]==0 for i in [1,2,5,6,10,11])
report={'status':'PASS','scope':'Exact first-variation elimination for the equal-D '
                'B-rank-one boundary over its six-dimensional splitting field. '
                'No companion infeasibility conclusion.',
        'sum_R':str(s),'field_relations':[str(f),str(g)],
        'field_basis':list(map(str,basis)),
        'R_kernel':['x','y',str(s-x-y)],'D_kernel':[1,1,1],
        'first_variation_determinant':str(det),
        'first_variation_determinant_inverse':str(det_inv),
        'companion_variables':['u','v','tau'],
        'D_companion':['0','u','v'],'B_companion':['1','tau','-1-tau'],
        'R_companion':list(map(str,sol)),
        'residuals':[{'index':i,'polynomial':str(a),
                      'degree':S.Poly(a,u,v,tau).total_degree(),
                      'terms':len(S.Poly(a,u,v,tau).terms())}
                     for i,a in enumerate(residuals) if a!=0],
        'seconds':time.monotonic()-start}
(base/f'trace-Bone-equal-D-linear-{which}.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'PASS','which':which,'seconds':report['seconds'],
                  'determinant':str(det),'residual_sizes':[(r['index'],r['degree'],r['terms'])
                                                         for r in report['residuals']]}),flush=True)
