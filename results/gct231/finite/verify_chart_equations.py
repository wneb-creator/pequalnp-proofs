import hashlib
import itertools
import json
from pathlib import Path
import random
import sys
import sympy as s

X = s.symbols('x y z')

for name in sys.argv[1:]:
    path = Path(name)
    data = json.loads(path.read_text())
    U = s.symbols(' '.join(data['unknowns']))
    names = {str(v): v for v in X + U}
    M = [[s.sympify(v, locals=names) for v in row] for row in data['matrix']]
    full = len(U) == 18
    assert len(U) in (9,18)
    expected_pivots = [[0,1],[0,2],[0,3]]
    assert data['pivots'] == expected_pivots
    assert data['remaining'] == [[1,2],[1,3],[2,3]]
    assert len(M) == 4 and all(len(row) == 4 for row in M)
    assert all(s.expand(M[i][j]-M[j][i]) == 0 for i in range(4) for j in range(4))
    assert all(M[i][j] == X[k] for k,(i,j) in enumerate(expected_pivots))
    assert all(s.expand(M[i][i]-sum(U[3*i+k]*X[k] for k in range(3))) == 0 for i in range(3))
    for n,(i,j) in enumerate(data['remaining']):
        expected = sum(U[9+3*n+k]*X[k] for k in range(3)) if full else 0
        assert s.expand(M[i][j]-expected) == 0
    assert s.expand(sum(sum(row) for row in M)) == 0
    domain = s.QQ.poly_ring(*U)
    A = [[s.Poly(1+v,*X,domain=domain) for v in row] for row in M]
    # Independent permanent algorithm: Ryser inclusion-exclusion over column subsets.
    permanent = s.Poly(0,*X,domain=domain)
    for mask in range(1,16):
        cols = [j for j in range(4) if mask & (1 << j)]
        term = s.Poly((-1)**(4-len(cols)),*X,domain=domain)
        for i in range(4):
            row_sum = s.Poly(0,*X,domain=domain)
            for j in cols:
                row_sum += A[i][j]
            term *= row_sum
        permanent += term
    residual = permanent - 24
    records = data['equations']
    assert len(records) == 31
    expected_monomials = {a for a in itertools.product(range(5),repeat=3) if 2 <= sum(a) <= 4}
    assert {tuple(r['monomial']) for r in records} == expected_monomials
    stored = s.Poly.from_dict({tuple(r['monomial']):s.sympify(r['coefficient'],locals=names)
                              for r in records},X,domain=domain)
    assert residual == stored
    # Additional independent ground checks against the direct 24-permutation definition.
    rng = random.Random(231)
    for _ in range(24):
        substitutions = {v:rng.randint(-3,3) for v in X+U}
        ground = [[1+int(v.subs(substitutions)) for v in row] for row in M]
        direct = sum(s.prod(ground[i][p[i]] for i in range(4))
                     for p in itertools.permutations(range(4))) - 24
        from_records = sum(s.sympify(r['coefficient'],locals=names).subs(substitutions)
                           * s.prod(substitutions[X[k]]**r['monomial'][k] for k in range(3))
                           for r in records)
        assert direct == from_records
    print(path.name, 'SHA256',hashlib.sha256(path.read_bytes()).hexdigest(),flush=True)
    print('PASS matrix normalization, tangent elimination, all31 coefficients, exact Ryser reconstruction,24 direct samples',flush=True)
