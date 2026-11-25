from pathlib import Path
import hashlib
import itertools
import json
import resource
import time
import sympy as S

resource.setrlimit(resource.RLIMIT_AS, (384 * 2**20, 384 * 2**20))
resource.setrlimit(resource.RLIMIT_CPU, (90, 95))
start = time.monotonic()
base = Path('/tmp/oec/pequalnp-pilot-78/geometry_search')
child = base / 'rowzero'
source = child / 'trace-Bone-systems.json'
certpath = child / 'trace-Bone-exceptional-certificate.json'
cert = json.loads(certpath.read_text())
assert hashlib.sha256(source.read_bytes()).hexdigest() == cert['source_sha256']
data = json.loads(source.read_text())['cases']['other-index']
names = {x: S.Symbol(x) for x in data['variables']}
alpha, u, v, s, t = S.symbols('alpha u v s t')
loc = dict(names, alpha=alpha, u=u, v=v)
parse = lambda x: S.sympify(x, locals=loc)
F = parse(cert['field_polynomial'])
red = lambda x: S.expand(S.rem(S.expand(x), F, alpha))
gens = list(map(parse, data['generators']))
sub = {names[k]: parse(value) for k, value in cert['normalization'].items()}
forced = {names[k]: parse(value) for k, value in cert['linear_solution'].items()}

# Rebuild the original physical matrix and its permanent by Ryser's formula,
# independently of the recorded polynomial formulas.
B = S.Matrix([parse(a)*s + parse(b)*t for a,b in data['B_forms']])
D = S.Matrix([parse(a)*s + parse(b)*t for a,b in data['D_forms']])
R = S.Matrix([parse(a)*s + parse(b)*t for a,b in data['R_forms']])
x = (R+2*D)/2
f = -R/2
M = S.Matrix([[0,x[0],x[1],x[2]],
              [x[0],B[0],f[2],f[1]],
              [x[1],f[2],B[1],f[0]],
              [x[2],f[1],f[0],B[2]]]).subs(sub, simultaneous=True)
H = S.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])
T = H*M*H/4
J = S.ones(4)
N = J+T
per = 0
for size in range(1,5):
    for subset in itertools.combinations(range(4),size):
        per += (-1)**(4-size)*S.prod(sum(N[i,j] for j in subset) for i in range(4))
poly = S.Poly(S.expand(per-24),s,t)
powers = [(d-j,j) for d in [2,3,4] for j in range(d+1)]
for i,power in enumerate(powers):
    assert S.expand(poly.coeff_monomial(s**power[0]*t**power[1]) -
                    parse(data['scales_to_actual_permanent_coefficients'][i]) *
                    gens[i].subs(sub, simultaneous=True)) == 0
assert poly.coeff_monomial(1) == poly.coeff_monomial(s) == poly.coeff_monomial(t) == 0

# The kernel classification is checked before either sign normalization.
ksub = {names['tau']:0,names['d1']:0,names['d3']:0}
q = S.expand(gens[2].subs(ksub))
c = S.expand(gens[6].subs(ksub))
p = S.expand(gens[11].subs(ksub)/16)
z = names['p3']
Fz = 5*z*z+14*z+10
assert S.expand(4*p-q*q/4-q*(2*z+3)-Fz)==0
assert S.expand(names['p1']**2+names['p5']**2-4*(z+1)**2+q+Fz)==0
assert c == -names['p1']*z*names['p5']
assert Fz.subs(z,0)==10 and Fz.subs(z,-1)==1

eqs = [S.expand(g.subs(sub, simultaneous=True)) for g in gens]
unknowns = [names[x] for x in ['p0','p2','p4']]
matrix,rhs = S.linear_eq_to_matrix([eqs[i] for i in cert['first_variation_indices']], unknowns)
matrix = matrix.applyfunc(red)
rhs = rhs.applyfunc(red)
assert matrix == S.Matrix([[parse(x) for x in row] for row in cert['linear_matrix']])
assert rhs == S.Matrix(list(map(parse,cert['linear_rhs'])))
det = parse(cert['linear_determinant_mod_F'])
assert red(matrix.det()-det)==0
assert S.expand(det*parse(cert['linear_determinant_inverse_mod_F']) +
                F*parse(cert['linear_determinant_Bezout_F_multiplier'])-1)==0
sol = S.Matrix([forced[x] for x in unknowns])
assert (matrix*sol-rhs).applyfunc(red)==S.zeros(3,1)
rawres = [S.expand(g.subs(forced, simultaneous=True)) for g in eqs]
res = list(map(red,rawres))
assert res == list(map(parse,cert['all_reduced_residuals']))
indices = cert['certificate_original_indices']
mult = list(map(parse,cert['certificate_multipliers']))
for rr,key in [(res,'certificate_F_multiplier_reduced'),
               (rawres,'certificate_F_multiplier_original_substituted')]:
    assert S.expand(sum(m*rr[i] for m,i in zip(mult,indices)) +
                    F*parse(cert[key])-cert['certificate_target']) == 0
kappa = parse(cert['residual_generators']['c2'])/(u*v)
assert S.expand(kappa*parse(cert['kappa_inverse_mod_F'])+
                F*parse(cert['kappa_Bezout_F_multiplier'])-1)==0
for action in cert['symmetry_actions']:
    P=S.zeros(4)
    for i,j in enumerate(action['vertex_permutation']): P[i,j]=1
    assert H*P*H/4 == S.Matrix([[parse(x) for x in row] for row in action['Hadamard_action']])
report = {'status':'PASS','certificate_sha256':hashlib.sha256(certpath.read_bytes()).hexdigest(),
          'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
          'direct_Ryser_coefficient_comparisons':12,
          'kernel_identities':True,'linear_inverse_and_solution':True,
          'reduced_and_original_certificate_identities':True,'vertex_symmetries':True,
          'scope':'Only the exceptional disjoint-support B-rank-one tracezero two-plane chart. Same-index chart remains open. Algebraic certificate, not a Lean theorem.',
          'seconds':time.monotonic()-start}
(base/'Bone-exceptional-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
