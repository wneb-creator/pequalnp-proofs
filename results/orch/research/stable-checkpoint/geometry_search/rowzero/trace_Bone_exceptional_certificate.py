from pathlib import Path
import hashlib
import json
import resource
import time

import sympy as S

resource.setrlimit(resource.RLIMIT_AS, (256 * 2**20, 256 * 2**20))
resource.setrlimit(resource.RLIMIT_CPU, (45, 50))
start = time.monotonic()
base = Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
source = base / 'trace-Bone-systems.json'
data = json.loads(source.read_text())['cases']['other-index']
names = {name: S.Symbol(name) for name in data['variables']}
alpha, u, v = S.symbols('alpha u v')
F = 5 * alpha**2 + 14 * alpha + 10


def red(e):
    return S.expand(S.rem(S.expand(e), F, alpha))


original = [S.sympify(g, locals=names) for g in data['generators']]
sub = {names['tau']: 0, names['d1']: 0, names['d3']: 0,
       names['p3']: alpha, names['p1']: -2 * (alpha + 1),
       names['p5']: 0, names['d0']: u, names['d2']: v}
equations = [S.expand(g.subs(sub, simultaneous=True)) for g in original]
unknowns = [names[k] for k in ['p0', 'p2', 'p4']]
indices = [1, 5, 10]
M, rhs = S.linear_eq_to_matrix([equations[i] for i in indices], unknowns)
M = M.applyfunc(red)
rhs = rhs.applyfunc(red)
det = red(M.det())
det_inv = S.invert(det, F, alpha)
det_bezout = S.div(S.expand(1 - det * det_inv), F, alpha)
assert det_bezout[1] == 0
inverse = (M.adjugate() * det_inv).applyfunc(red)
assert (M * inverse - S.eye(3)).applyfunc(red) == S.zeros(3)
solution = (inverse * rhs).applyfunc(red)
expected = S.Matrix([u * (-5 - S.Rational(12, 5) * alpha),
                     u * (4 + S.Rational(16, 5) * alpha),
                     v * (-alpha - S.Rational(14, 5))])
assert (solution - expected).applyfunc(S.expand) == S.zeros(3, 1)
sub2 = dict(zip(unknowns, solution))
substituted = [S.expand(g.subs(sub2, simultaneous=True)) for g in equations]
residuals = [red(g) for g in substituted]
assert all(residuals[i] == 0 for i in indices)

A = 15 + S.Rational(48, 5) * alpha
B = S.Rational(124, 25) + S.Rational(16, 5) * alpha
gamma = S.Rational(16, 5) + S.Rational(44, 25) * alpha
kappa = S.Rational(34, 5) + S.Rational(24, 5) * alpha
q = A * u**2 + B * v**2 + 2
c3 = u**2 - v**2 + gamma * u**2 * v
c2 = kappa * u * v
assert S.expand(residuals[0] - q) == 0
assert S.expand(residuals[3] - c3) == 0
assert S.expand(residuals[4] - c2) == 0
kappa_inv = S.invert(kappa, F, alpha)
kappa_bezout = S.div(S.expand(1 - kappa * kappa_inv), F, alpha)
assert kappa_bezout[1] == 0
K = A + B
m0 = red(2 - K * u**2)
m3 = red(K * A * u**2 + 2 * B)
m4 = red((K**2 * u * v - gamma * u * m3) * kappa_inv)
reduced_combination = S.expand(m0 * q + m3 * c3 + m4 * c2 - 4)
mF, remainder = S.div(-reduced_combination, F, alpha)
assert remainder == 0
assert S.expand(m0 * q + m3 * c3 + m4 * c2 + mF * F) == 4

# Also verify the certificate against the original generators after the
# forced linear substitution, rather than only their residue classes.
direct = S.expand(m0 * substituted[0] + m3 * substituted[3] +
                  m4 * substituted[4] - 4)
direct_F, remainder = S.div(-direct, F, alpha)
assert remainder == 0
assert S.expand(m0 * substituted[0] + m3 * substituted[3] +
                m4 * substituted[4] + direct_F * F) == 4

# The two reductions to the chosen kernel sign are actual vertex relabelings.
H = S.Matrix([[1, 1, 1, 1], [1, 1, -1, -1],
              [1, -1, 1, -1], [1, -1, -1, 1]])
actions = []
for perm, expected_action in [
        ([0, 3, 2, 1], S.Matrix([[1, 0, 0, 0], [0, 0, 0, 1],
                                [0, 0, 1, 0], [0, 1, 0, 0]])),
        ([2, 3, 0, 1], S.diag(1, -1, 1, -1))]:
    P = S.zeros(4)
    for i, j in enumerate(perm):
        P[i, j] = 1
    action = H * P * H / 4
    assert action == expected_action
    actions.append({'vertex_permutation': perm,
                    'Hadamard_action': [[str(x) for x in row]
                                        for row in action.tolist()]})

report = {
    'status': 'PASS', 'source': str(source),
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'scope': 'Exact exclusion of the exceptional disjoint-support B-rank-one '
             'chart. The same-index B-rank-one chart is not excluded here. '
             'This is an algebraic certificate, not a Lean theorem.',
    'field_polynomial': str(F),
    'normalization': {str(k): str(value) for k, value in sub.items()},
    'first_variation_indices': indices,
    'linear_matrix': [[str(x) for x in row] for row in M.tolist()],
    'linear_rhs': list(map(str, rhs)),
    'linear_determinant_mod_F': str(det),
    'linear_determinant_inverse_mod_F': str(det_inv),
    'linear_determinant_Bezout_F_multiplier': str(det_bezout[0]),
    'linear_solution': {str(k): str(value) for k, value in sub2.items()},
    'all_reduced_residuals': list(map(str, residuals)),
    'residual_generators': {'q': str(q), 'c3': str(c3), 'c2': str(c2)},
    'kappa_inverse_mod_F': str(kappa_inv),
    'kappa_Bezout_F_multiplier': str(kappa_bezout[0]),
    'certificate_target': 4,
    'certificate_original_indices': [0, 3, 4],
    'certificate_multipliers': list(map(str, [m0, m3, m4])),
    'certificate_F_multiplier_reduced': str(S.expand(mF)),
    'certificate_F_multiplier_original_substituted': str(S.expand(direct_F)),
    'symmetry_actions': actions,
    'coverage': ['If the B and D_B supports overlap, the same-index chart applies.',
                 'Otherwise nonzero sum-zero B has exactly two supported entries '
                 'and D_B is supported on its missing coordinate: the exceptional chart.',
                 'Its kernel equations imply F(p3)=0, p1*p5=0, and '
                 'p1^2+p5^2=4*(p3+1)^2; F(0)=10 and F(-1)=1.',
                 'The checked axis swap, accompanied by negating A, sets p5=0. '
                 'The checked even sign flip sets p1=-2*(p3+1).',
                 'The invertible three first variations force the recorded solution.',
                 'The three remaining residuals have an exact polynomial combination '
                 'equal to 4 modulo F, hence no complex solution.'],
    'seconds': time.monotonic() - start}
(base / 'trace-Bone-exceptional-certificate.json').write_text(
    json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'seconds': report['seconds'],
                  'determinant_mod_F': str(det),
                  'residual_certificate_terms': sum(len(S.Poly(m, u, v).terms())
                                                     for m in [m0, m3, m4]),
                  'scope': report['scope']}), flush=True)
