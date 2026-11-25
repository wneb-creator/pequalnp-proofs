"""Independently reconstruct a sparse neogb QQ input and compare all rows."""
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
lengths = list(map(int, lines[1].split()))
assert characteristic == 0
assert n == len(variables) and m == len(data['equations']) == len(lengths)
assert sum(lengths) == term_count and len(lines) == term_count + 2
offset = 2
for index, (equation, length) in enumerate(zip(data['equations'], lengths)):
    terms = {}
    for line in lines[offset:offset + length]:
        numerator, denominator, *exponents = map(int, line.split())
        assert len(exponents) == n and denominator != 0
        assert all(exponent >= 0 for exponent in exponents)
        exponents = tuple(exponents)
        assert exponents not in terms
        terms[exponents] = s.Rational(numerator, denominator)
    actual = s.Poly.from_dict(terms, variables, domain=s.QQ)
    expected = s.Poly(s.sympify(equation['coefficient'],
        locals=dict(zip(data['unknowns'], variables))), *variables, domain=s.QQ)
    expected = expected.clear_denoms()[1].primitive()[1]
    assert actual == expected, (index, actual - expected)
    offset += length
print('PASS exact QQ input roundtrip:', m, 'polynomials,', term_count, 'terms')
print('Source SHA256:', hashlib.sha256(args.source.read_bytes()).hexdigest())
print('Input SHA256:', hashlib.sha256(args.input.read_bytes()).hexdigest())
