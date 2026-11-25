"""Rebuild the star-support coefficient equations by permanent subset DP."""
from pathlib import Path
from fractions import Fraction
import json
import hashlib
import sympy as s
from verify_certificate import input_polynomials

base = Path(__file__).resolve().parent.parent
path = base/'star-support-buchberger-equations.json'
raw = json.loads(path.read_text())
names, source = input_polynomials(base/'qq-star-support.in')
assert names == raw['unknowns']
variables = s.symbols(' '.join(names))
x,y,z = s.symbols('x y z')
local = dict(zip(names,variables)) | dict(x=x,y=y,z=z)
matrix = [[s.sympify(cell,locals=local) for cell in row] for row in raw['matrix']]
assert all(matrix[i][j] == matrix[j][i] for i in range(4) for j in range(4))
assert s.expand(sum(sum(row) for row in matrix)) == 0
assert [matrix[0][1],matrix[0][2],matrix[0][3]] == [x,y,z]
assert matrix[1][2] == matrix[1][3] == matrix[2][3] == 0
# Subset dynamic programming, independent of the author's 24-permutation loop.
partial = {0:s.Integer(1)}
for row in range(4):
    nxt = {}
    for mask,polynomial in partial.items():
        for col in range(4):
            if not (mask >> col)&1:
                target = mask | (1<<col)
                nxt[target] = nxt.get(target,0) + polynomial*(1+matrix[row][col])
    partial = {mask:s.expand(polynomial) for mask,polynomial in nxt.items()}
permanent = s.Poly(partial[15]-24,x,y,z)
expected = {tuple(term['monomial']):s.expand(s.sympify(term['coefficient'],locals=local)) for term in raw['equations']}
assert len(expected) == len(raw['equations']) == 31
assert dict(permanent.terms()) == expected
scalings = []
for idx,equation in enumerate(raw['equations']):
    polynomial = s.Poly(expected[tuple(equation['monomial'])],*variables,domain=s.QQ)
    content, primitive = polynomial.primitive()
    exact = {tuple(mon):Fraction(int(coefficient.p),int(coefficient.q)) for mon,coefficient in primitive.terms()}
    assert exact == source[idx], ('source conversion',idx)
    scalings.append(str(content))
print(json.dumps(dict(verdict='PASS',source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
    source_equations=31, method='permanent subset DP; exact QQ primitive polynomial comparison',
    input_sha256=hashlib.sha256((base/'qq-star-support.in').read_bytes()).hexdigest(),
    scalings=scalings)))
