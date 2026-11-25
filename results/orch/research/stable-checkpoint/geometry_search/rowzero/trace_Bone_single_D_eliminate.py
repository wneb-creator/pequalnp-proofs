from pathlib import Path
import json
import hashlib
import resource
import time
import sympy as S

resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(45,50))
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
data=json.loads((base/'trace-Bone-single-D.json').read_text())
u,v,tau,U,T=S.symbols('d0 d2 tau U T')
eq={r['index']:S.expand(S.sympify(r['polynomial'],locals={'d0':u,'d2':v,'tau':tau}))
    for r in data['residuals']}
kappa=(2+24*S.I)/25
v0=-S.Rational(93,116)-11*S.I/29
assert S.expand(eq[4]-kappa*u*(v-v0))==0
assert S.expand(eq[3].subs(u,0)+(tau+1)*(v**2+tau))==0
report={'scope':'Further exact case elimination of the kernel-D-support-one '
                'specialization over QQ(i); no generic B-rank-one conclusion.',
        'input_sha256':hashlib.sha256((base/'trace-Bone-single-D.json').read_bytes()).hexdigest(),
        'split':'d0=0 or d2='+str(v0),'branches':{}}
for name,sub in [('u-zero-tau-minus-one',{u:0,tau:-1}),
                 ('u-zero-tau-minus-v-squared',{u:0,tau:-v**2})]:
    fs=[S.Poly(eq[i].subs(sub,simultaneous=True),v,extension=S.I) for i in [0,9]]
    left,right,gcd=S.gcdex(fs[0],fs[1])
    assert left*fs[0]+right*fs[1]==gcd
    assert gcd.as_expr()==1
    report['branches'][name]={'generators':[str(f.as_expr()) for f in fs],
                              'gcd':str(gcd.as_expr()),
                              'multipliers':[str(left.as_expr()),str(right.as_expr())]}

fs=[eq[0],eq[9],S.cancel(eq[8]/u)]
fs=[S.expand(f.subs(v,v0)).subs(u**2,U).subs(tau**2,T) for f in fs]
M,rhs=S.linear_eq_to_matrix(fs,[U,T,tau])
sol=list(S.linsolve((M,rhs),[U,T,tau]))
report['branches']['v-fixed-u-nonzero']={
    'generators':list(map(str,fs)),'linear_rank':M.rank(),
    'augmented_rank':M.row_join(rhs).rank(),
    'linear_matrix':[[str(x) for x in row] for row in M.tolist()],
    'linear_rhs':list(map(str,rhs)),
    'linear_determinant':str(S.expand(M.det())),
    'linear_solution':[list(map(str,s)) for s in sol]}
if sol and len(sol)==1:
    assert (M*S.Matrix(sol[0])-rhs).applyfunc(S.expand)==S.zeros(3,1)
    constraint=S.simplify(sol[0][1]-sol[0][2]**2)
    assert constraint!=0 and not constraint.free_symbols
    report['branches']['v-fixed-u-nonzero']['T_minus_tau_squared']=str(constraint)
else:
    raise AssertionError('Expected a unique incompatible linear solution')
report['status']='PASS: all three branches are impossible'
report['coverage']=[
    'Kernel D=(1,0,0) implies F(p1)=5p1^2+14p1+10=0, p3*p5=0, and '
    'p3^2+p5^2=4*(p1+1)^2. F(0)=10 and F(-1)=1.',
    'Swapping axes 1 and 2 sets p5=0; an even sign flip of axes 1 and 2 '
    'sets p3=-2*(p1+1). Both fix D=(1,0,0) and preserve the '
    'normalized trace-zero B-companion family (1,tau,-1-tau).',
    'The field root (-7+I)/5 and its complex conjugate exhaust F. '
    'All original generator coefficients are rational, so conjugation '
    'transfers every exact identity to the other root.',
    'The mixed cubic factors as a nonzero scalar times u*(v-v0). '
    'For u=0 the cubic factors as -(tau+1)*(v^2+tau), giving the first two branches.',
    'For u nonzero and v=v0, division of the quartic residual by u is valid. '
    'Three linear equations in (u^2,tau^2,tau) force incompatible '
    'values of tau^2 and the square of tau.']
report['seconds']=time.monotonic()-start
(base/'trace-Bone-single-D-eliminate.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2),flush=True)
