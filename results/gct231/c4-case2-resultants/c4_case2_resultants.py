"""Bounded necessary-equation reduction for C4 case2 over its scale curve."""
from pathlib import Path
import json
import time
import sympy as S

base = Path(__file__).parent
P, B, U, V, sat = S.symbols('P B U V sat')
local = {str(x): x for x in (P, B, U, V, sat)}
source = json.loads((base / 'fresh/c4-nonzero-reduced-2.json').read_text())
equations = [S.sympify(x, locals=local) for x in source['equations']]
F = equations[2]
K = P**2 + P - 1
assert S.expand(F - (K * (-6*B**2 + (5*P**2-P+10)*B - 8*P**2) - 3*P*B)) == 0
safe = P * B * K * (9*B**2 - 6*B*P**2 - 12*B + 10*P**2)
field = S.QQ.frac_field(P, U, V)
modulus = S.Poly(F, B, domain=field)
start = time.monotonic()
reductions = []

def reduce_curve(expression, label):
    quotient, remainder = S.div(S.Poly(expression, B, domain=field), modulus)
    rational = S.cancel(remainder.as_expr())
    numerator, denominator = S.fraction(rational)
    assert denominator.free_symbols <= {P}
    polynomial = S.Poly(numerator, P, B, U, V, domain=S.QQ).clear_denoms()[1].primitive()[1].as_expr()
    factors_removed = []
    while polynomial != 0:
        common = S.gcd(polynomial, safe)
        if S.Poly(common, P, B, U, V).total_degree() == 0:
            break
        polynomial = S.cancel(polynomial / common)
        factors_removed.append(str(common))
    reductions.append({'label': label, 'denominator': str(denominator),
                       'removed_nonzero_factors': factors_removed, 'polynomial': str(polynomial)})
    degree = S.Poly(polynomial, P, B, U, V).total_degree()
    terms = len(S.Poly(polynomial, P, B, U, V).terms())
    print(label, {'degree': degree, 'terms': terms, 'seconds': time.monotonic()-start}, flush=True)
    (base / 'c4-case2-resultant-progress.json').write_text(json.dumps(reductions, indent=2) + '\n')
    return polynomial

q = reduce_curve(equations[0], 'q')
c = reduce_curve(equations[1], 'c')
r = reduce_curve(equations[3], 'linear_r')
l = reduce_curve(equations[4], 'quadratic_l')
assert S.degree(r, U) <= 1
outputs = []
for polynomial, label in ((q, 'q'), (c, 'c'), (l, 'l')):
    resultant = S.resultant(r, polynomial, U)
    outputs.append(reduce_curve(resultant, 'eliminate_U_' + label))
for (i, j) in ((0, 1), (0, 2), (1, 2)):
    resultant = S.resultant(outputs[i], outputs[j], V)
    reduce_curve(resultant, 'eliminate_V_' + str(i) + str(j))
(base / 'c4-case2-resultants.json').write_text(json.dumps({'source': source,
    'scale_curve': str(F), 'known_nonzero_K': str(K), 'safe_factors': str(safe),
    'reductions': reductions,
    'scope': 'Necessary resultants only; no branch exclusion until independently checked.'}, indent=2) + '\n')
