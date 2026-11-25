"""Independent source/formula review of the frozen higher coefficient bridge."""
from pathlib import Path
from itertools import product
import hashlib
import json
import re
import sympy as s

base = Path('/tmp/oec/pequalnp-pilot-75/gct231')
path = base / 'library/FullStarHigherCoefficients.lean'
text = path.read_text()
sha = hashlib.sha256(path.read_bytes()).hexdigest()
assert sha == '73002c5f10b0087f85d3bc176b439e2243a8b54a2cca3992de54b78fdfcc9b62'
old = (base / 'library/FullStarCoefficient.lean').read_text()
foundation = old.rsplit('end PEqualNP.Outside.L_gct_231_aux.Coeff', 1)[0].rstrip()
assert text.startswith(foundation)
data = json.loads((base / 'star-full-generate-equations.json').read_text())
for monomial, count in [([1, 1, 1], 2), ([2, 1, 1], 3)]:
    literal = next(eq['coefficient'] for eq in data['equations']
                   if eq['monomial'] == monomial).replace('**', '^')
    assert text.count(literal) == count, (monomial, text.count(literal))
    print('PASS exact coefficient literal:', monomial, 'occurrences', count)
names = [f'{letter}{index}' for letter in 'abcd' for index in range(3)]
variables = s.symbols(names)
namespace = dict(zip(names, variables))
rows = [variables[i:i+3] for i in range(0, 12, 3)]
for name, target, factor in [('triple_four_affine', (1, 1, 1), 1),
                              ('quartic_four_affine', (2, 1, 1), 2)]:
    theorem = text.split('theorem ' + name, 1)[1].split('\n\ntheorem', 1)[0]
    formula = theorem.split(' =\n', 1)[1].split(' := by', 1)[0].strip()
    observed = s.sympify(formula.replace('^', '**'), locals=namespace)
    expected = 0
    for choices in product(range(4), repeat=4):
        counts = tuple(choices.count(i+1) for i in range(3))
        if counts == target:
            term = s.Integer(factor)
            for row, choice in zip(rows, choices):
                if choice:
                    term *= row[choice-1]
            expected += term
    assert s.expand(observed-expected) == 0
    print('PASS independent affine-product enumeration:', name)
assert 'MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p))' in text
assert 'MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0\n      (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p)))' in text
assert 'quartic p = 2 * p.coeff' in text
assert '(Finsupp.single 0 2 + Finsupp.single 1 1 + Finsupp.single 2 1)' in text
print('PASS unchanged reviewed matrix/XY foundation and derivative multiplicities.')
print('SHA256:', sha)
print('Source review only; library_route independently reports Lean build exit0.')
