from pathlib import Path
import json
import sympy as s

root = Path('/tmp/oec/pequalnp-pilot-78')
data = json.loads((root / 'construct_search/net_normal_form/c3-tracezero-system.json').read_text())
w, a, b, c, d, X, Y, B, D = s.symbols('w a b c d X Y B D')
env = {str(v): v for v in (w, a, b, c, d)}
U = s.Matrix([[s.sympify(e, locals=env) for e in row] for row in data['U']])
V = s.Matrix([[s.sympify(e, locals=env) for e in row] for row in data['V']])
assert U == U.T and V == V.T
relation = s.Poly(w*w+w+1, w)
def red(expression):
    return s.Poly(s.expand(expression), w).rem(relation).as_expr().expand()
assert red(s.trace(U)) == red(s.trace(V)) == 0
M = s.ones(4) + X*U + Y*V
ryser = 0
for mask in range(16):
    columns = [j for j in range(4) if mask & (1 << j)]
    ryser += (-1)**(4-len(columns))*s.prod(sum(M[i,j] for j in columns) for i in range(4))
polynomial = s.Poly(red(ryser-24), X, Y)
assert set(polynomial.monoms()) == {(1,1),(3,0),(0,3),(2,2)}
for exponent, recorded in zip(((1,1),(3,0),(0,3),(2,2)), data['equations']):
    assert red(polynomial.coeff_monomial(X**exponent[0]*Y**exponent[1]) - s.sympify(recorded, locals=env)) == 0
normalized = [red(polynomial.coeff_monomial(X**i*Y**j).subs({b:w*B,d:w*w*D}))
              for i,j in ((1,1),(3,0),(0,3),(2,2))]
q = -a*c+2*a*D+2*B*c-2*a-2*c+2*B+2*D
def cubic(x,y):
    return x**3+6*x**2+3*x*y**2-6*x*y+3*x+2*y**3+6*y
p = (a-c)**2+2*(a-c)*(B-D)+3*(B+D)**2
proposed = [q,cubic(a,B),cubic(c,D),p]
scales = []
for actual, target in zip(normalized, proposed):
    ratio = s.cancel(actual/target)
    assert not ratio.free_symbols and ratio != 0
    assert s.expand(actual-ratio*target) == 0
    scales.append(str(ratio))
result = {'status':'PASS','method':'Independent sixteen-subset Ryser expansion',
          'symmetry_and_trace':True,'only_four_nonconstant_coefficients':True,
          'all_recorded_equations_match':True,'rational_normalization_scales':scales,
          'scope':'Equations for the C3-invariant plane ansatz only; no exhaustive global classification.'}
(root/'root-algebra/c3-tracezero-independent-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
