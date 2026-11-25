"""Check the frozen Lean full-star XY coefficient against reviewed CAS data."""
from pathlib import Path
import hashlib
import json
import re
import sympy as s

base = Path('/tmp/oec/pequalnp-pilot-75/gct231')
lean_path = base / 'library/FullStarCoefficient.lean'
json_path = base / 'star-full-generate-equations.json'
text = lean_path.read_text()
expected_hash = '4deb2bc9e8e6747c515336f607194f8a07b965e540b40a7274d3e72d1cea2d35'
assert hashlib.sha256(lean_path.read_bytes()).hexdigest() == expected_hash
data = json.loads(json_path.read_text())
names = [f'd{i}' for i in range(9)] + [f'o{i}' for i in range(9)]
assert data['unknowns'] == names
assert data['pivots'] == [[0, 1], [0, 2], [0, 3]]
variables = s.symbols(names)
namespace = dict(zip(names, variables))
x, y, z = s.symbols('x y z')
namespace.update(x=x, y=y, z=z)
d = variables[:9]
o = variables[9:]
lin = lambda a, b, c: a*x + b*y + c*z
matrix = [
    [lin(*d[:3]), x, y, z],
    [x, lin(*d[3:6]), lin(*o[:3]), lin(*o[3:6])],
    [y, lin(*o[:3]), lin(*d[6:]), lin(*o[6:])],
    [z, lin(*o[3:6]), lin(*o[6:]), lin(
        -(d[0]+d[3]+d[6]+2*(1+o[0]+o[3]+o[6])),
        -(d[1]+d[4]+d[7]+2*(1+o[1]+o[4]+o[7])),
        -(d[2]+d[5]+d[8]+2*(1+o[2]+o[5]+o[8])))],
]
for i in range(4):
    for j in range(4):
        assert s.expand(matrix[i][j]-s.sympify(data['matrix'][i][j], locals=namespace)) == 0
literal = next(eq['coefficient'] for eq in data['equations']
               if eq['monomial'] == [1, 1, 0])
assert text.count(literal) == 2
assert re.search(r'def affine3.*?1 \+ MvPolynomial.C a', text, re.S)
assert 'Finsupp.single 0 1 + Finsupp.single 1 1' in text
print('PASS frozen Lean source hash:', expected_hash)
print('PASS exact 18-parameter order and all16 matrix entries against reviewed JSON.')
print('PASS literal XY polynomial occurs identically in coefficient theorem and zero corollary.')
print('Manual source check: affine3 adds the all-ones matrix; mixed is pderiv0 pderiv1 at0.')
print('The mixed derivative selects XY with factorial1. The zero corollary assumes the')
print('full polynomial identity and uses mixed_nat24. No algebraic inconsistency is claimed.')
print('Build status is independently supplied by library_route; this review does not rerun Lean.')
