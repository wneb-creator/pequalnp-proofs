from pathlib import Path
from itertools import permutations
import json
import resource
import time
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(45,50))
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
data=json.loads((base/'trace-Bone-systems.json').read_text())['cases']['same-index']
names={name:S.Symbol(name) for name in data['variables']}
gens=[S.sympify(g,locals=names) for g in data['generators']]
x,y,u,v,tau=S.symbols('x y u v tau')
which=9;s=-S.Rational(which,2);e2=s*s/2+3*s+9;e3=2*s+6
f=x**3-s*x*x+e2*x-e3
g=y*y+(x-s)*y+x*x-s*x+e2
K,yr,xr,ur,vr,tr=ring('y,x,u,v,tau',QQ)
relations=[K.from_expr(g),K.from_expr(f)]

def red(a):return a.div(relations)[1]
def from_expr(a):return red(K.from_expr(S.expand(a)))
def product(elements):
    result=K.one
    for a in elements:result=red(result*a)
    return result

basis=[xr**i*yr**j for j in range(2) for i in range(3)]
def inverse(a):
    columns=[]
    for b in basis:
        c=red(a*b)
        column=[]
        for j in range(2):
            for i in range(3):
                q=c.get((j,i,0,0,0),QQ.zero)
                column.append(S.Rational(int(q.numerator),int(q.denominator)))
        columns.append(S.Matrix(column))
    values=S.Matrix.hstack(*columns).inv()*S.Matrix([1,0,0,0,0,0])
    ans=sum(QQ(int(z.p),int(z.q))*b for z,b in zip(values,basis))
    assert red(a*ans)==1
    return ans

sub={names['d1']:1,names['d3']:1,names['p1']:x,
     names['p3']:y,names['p5']:s-x-y,
     names['d0']:u,names['d2']:v,names['tau']:tau}
unknowns=[names[k] for k in ['p0','p2','p4']]
indices=[1,5,10]
M,rhs=S.linear_eq_to_matrix([S.expand(gens[i].subs(sub,simultaneous=True)) for i in indices],unknowns)
mat=[[from_expr(a) for a in row] for row in M.tolist()]
b=[from_expr(a) for a in rhs]
det=K.zero
for perm in permutations(range(3)):
    inversions=sum(perm[i]>perm[j] for i in range(3) for j in range(i+1,3))
    det+=(-1)**inversions*product([mat[i][perm[i]] for i in range(3)])
det=red(det);det_inv=inverse(det)
inv=[[K.zero for _ in range(3)] for _ in range(3)]
for i,j in [(i,j) for i in range(3) for j in range(3)]:
    rows=[k for k in range(3) if k!=j]
    cols=[k for k in range(3) if k!=i]
    cofactor=(-1)**(i+j)*(mat[rows[0]][cols[0]]*mat[rows[1]][cols[1]]-
                         mat[rows[0]][cols[1]]*mat[rows[1]][cols[0]])
    inv[i][j]=red(cofactor*det_inv)
for i,j in [(i,j) for i in range(3) for j in range(3)]:
    assert red(sum(mat[i][k]*inv[k][j] for k in range(3)))==int(i==j)
sol=[red(sum(inv[i][k]*b[k] for k in range(3))) for i in range(3)]
values={name:from_expr(value) for name,value in sub.items()}
values.update(dict(zip(unknowns,sol)))
powers={name:[K.one] for name in names.values()}
for name in names.values():
    for degree in range(1,5):powers[name].append(red(powers[name][-1]*values[name]))
residuals=[]
for h in gens:
    result=K.zero
    for monomial,coefficient in S.Poly(h,*names.values()).terms():
        term=QQ(int(coefficient.p),int(coefficient.q))*product(
            [powers[name][degree] for name,degree in zip(names.values(),monomial) if degree])
        result+=term
    residuals.append(red(result))
assert all(residuals[i]==0 for i in [1,2,5,6,10,11])
report={'status':'PASS','scope':'Exact first-variation elimination for the equal-D '
                'B-rank-one boundary over its six-dimensional splitting field. '
                'No companion infeasibility conclusion.',
        'sum_R':str(s),'field_relations':[str(f),str(g)],
        'field_basis':[str(b) for b in basis],
        'R_kernel':['x','y',str(s-x-y)],'D_kernel':[1,1,1],
        'first_variation_determinant':str(det),
        'first_variation_determinant_inverse':str(det_inv),
        'companion_variables':['u','v','tau'],
        'D_companion':['0','u','v'],'B_companion':['1','tau','-1-tau'],
        'R_companion':list(map(str,sol)),
        'residuals':[{'index':i,'polynomial':str(a),
                      'degree':max(sum(m[2:]) for m in a),
                      'terms':len({m[2:] for m in a})}
                     for i,a in enumerate(residuals) if a],
        'seconds':time.monotonic()-start}
(base/f'trace-Bone-equal-D-linear-{which}.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'PASS','which':which,'seconds':report['seconds'],
                  'determinant':str(det),'residual_sizes':[(r['index'],r['degree'],r['terms'])
                                                         for r in report['residuals']]}),flush=True)
