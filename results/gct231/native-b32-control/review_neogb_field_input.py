"""Independently compare every sparse finite-field input row with its source."""
import argparse
import hashlib
import json
from pathlib import Path
import sympy as s

parser = argparse.ArgumentParser()
parser.add_argument('source', type=Path)
parser.add_argument('input', type=Path)
args = parser.parse_args()
data = json.loads(args.source.read_text())
variables = s.symbols(data['unknowns'])
lines = args.input.read_text().splitlines()
n, m, characteristic, term_count = map(int, lines[0].split())
assert s.isprime(characteristic)
lengths = list(map(int, lines[1].split()))
assert n == len(variables) and m == len(data['equations']) == len(lengths)
assert sum(lengths) == term_count and len(lines) == term_count + 2
offset = 2
for index, (equation, length) in enumerate(zip(data['equations'], lengths)):
    terms = {}
    for line in lines[offset:offset+length]:
        numerator, denominator, *exponents = map(int, line.split())
        assert len(exponents) == n and denominator % characteristic != 0
        assert all(exponent >= 0 for exponent in exponents)
        monomial = tuple(exponents)
        assert monomial not in terms
        terms[monomial] = numerator * pow(denominator, -1, characteristic) % characteristic
    actual = s.Poly.from_dict(terms, variables, modulus=characteristic)
    original = s.Poly(s.sympify(equation['coefficient'],
        locals=dict(zip(data['unknowns'], variables))), *variables, domain=s.QQ)
    denominator, integral = original.clear_denoms()
    content, primitive = integral.primitive()
    assert int(denominator) % characteristic and int(content) % characteristic
    expected = s.Poly(primitive.as_expr(), *variables, modulus=characteristic)
    assert actual == expected, index
    offset += length
print('PASS every finite-field row:', m, 'polynomials,', term_count, 'terms, prime', characteristic)
print('Source SHA256:', hashlib.sha256(args.source.read_bytes()).hexdigest())
print('Input SHA256:', hashlib.sha256(args.input.read_bytes()).hexdigest())
