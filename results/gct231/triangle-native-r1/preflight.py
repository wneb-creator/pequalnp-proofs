from pathlib import Path
import hashlib
import json
import sympy as sp

base = Path('/tmp/oec/pequalnp-pilot-75/gct231')
run = base / 'triangle-native-r1'
source = base / 'triangle_concept/triangle-twelve-equations.json'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(source) == '03a8aa61b2a83e2918457d922059fb481128cc02b3d1532c2cfcc11677ed0ce7'
data = json.loads(source.read_text())
meta = json.loads((run / 'triangle-p1009.provenance.json').read_text())
assert digest(source) == meta['source_sha256']
inp = run / 'triangle-p1009.in'
assert digest(inp) == meta['input_sha256']
names = data['unknowns']
variables = sp.symbols(names)
with inp.open() as stream:
    n, m, p, total = map(int, stream.readline().split())
    lengths = list(map(int, stream.readline().split()))
    assert (n, m, p, total) == (12, 26, 1009, 686)
    assert len(lengths) == m and sum(lengths) == total
    assert len(data['equations']) == m and len(variables) == n
    for index, length in enumerate(lengths):
        terms = {}
        for _ in range(length):
            num, den, *exponents = map(int, stream.readline().split())
            assert len(exponents) == n and min(exponents) >= 0
            exponents = tuple(exponents)
            assert exponents not in terms and den == 1 and num % p != 0
            terms[exponents] = sp.Rational(num, den)
        encoded = sp.Poly.from_dict(terms, variables, domain=sp.QQ)
        original = sp.Poly(sp.sympify(data['equations'][index]['coefficient'],
                                     locals=dict(zip(names, variables))),
                           *variables, domain=sp.QQ)
        scale = meta['equation_scalings'][index]
        numerator = sp.Rational(scale['content'])
        denominator = sp.Rational(scale['denominator'])
        assert numerator % p != 0 and denominator % p != 0
        assert encoded * numerator == original * denominator
        print('equation', index, 'exact scaled coefficient equality PASS', length)
    assert not stream.read().strip()
engine = base / 'sparse-engine'
review = Path('/workspace/pequalnp-proofs/results/gct231/checkpoint-subset-review/source-hashes.json')
for relative, expected in json.loads(review.read_text()).items():
    assert digest(base / relative) == expected, relative
provenance = json.loads((engine / 'checkpoint-subset/provenance.json').read_text())
for relative, expected in provenance['files'].items():
    assert digest(engine / relative) == expected, relative
print('reviewed checkpoint-subset provenance: all 21 hashes PASS')
print('Scope: necessary reduced triangle equations over F1009 only; no complex-field conclusion.')
print('PREFLIGHT PASS', digest(inp))
