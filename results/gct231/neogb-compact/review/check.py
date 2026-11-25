"""Independent exact checks of compact M-record provenance and certificates."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import sympy as s

base = Path('/tmp/oec/pequalnp-pilot-75/gct231')
old_dir = base / 'sparse-engine/certificate-trace'
new_dir = base / 'sparse-engine/certificate-trace-compact'
for relative, prefix in [
    ('sparse-engine/cert_trace_compact.c', '107f123f'),
    ('sparse-engine/make_cert_trace_compact.py', '0d31a55c'),
    ('sparse-engine/run_neogb_trace_compact.py', '85db8c94'),
    ('replay_neogb_compact.py', 'a8151e72'),
]:
    digest = hashlib.sha256((base / relative).read_bytes()).hexdigest()
    assert digest.startswith(prefix)
    print('Frozen source:', relative, digest)

for name in ['toy-unit', 'toy-nonunit', 'toy-rational', 'rowzero']:
    certificate = json.loads((new_dir / f'{name}.certificate.json').read_text())
    names = certificate['variables']
    variables = s.symbols(names)
    namespace = dict(zip(names, variables))
    def parse(text):
        return s.Poly(s.sympify(text.replace('^', '**'), locals=namespace),
                      *variables, domain=s.QQ)
    old_records = [line.split('\t') for line in
                   (old_dir / f'{name}.trace').read_text().splitlines()]
    old_inputs = {int(row[1]): parse(row[2]) for row in old_records if row[0] == 'I'}
    old_outputs = {int(row[1]): parse(row[2]) for row in old_records if row[0] == 'O'}
    verified_outputs = {}
    count_m = count_o = 0
    for row in [line.split('\t') for line in
                (new_dir / f'{name}.trace').read_text().splitlines()]:
        if row[0] == 'M':
            node, parent = int(row[1]), int(row[2])
            shift = tuple(map(int, row[3].split(',')))
            assert len(shift) == len(variables) and all(i >= 0 for i in shift)
            assert parent in verified_outputs
            monomial = s.prod(x**e for x, e in zip(variables, shift))
            assert verified_outputs[parent] * s.Poly(monomial, *variables) == old_inputs[node]
            count_m += 1
        elif row[0] == 'I':
            assert parse(row[2]) == old_inputs[int(row[1])]
        elif row[0] == 'O':
            node = int(row[1])
            observed = parse(row[2])
            assert observed == old_outputs[node]
            verified_outputs[node] = observed
            count_o += 1
    companion = Path(certificate['input']).read_text().splitlines()
    _, variable_count, generator_count = map(int, companion[0].split())
    assert variable_count == len(variables)
    generators = [parse(line) for line in companion[2:2+generator_count]]
    steps = {}
    for step in certificate['steps']:
        index = step['index']
        terms = {tuple(exponents): s.Rational(coefficient)
                 for exponents, coefficient in step['polynomial']}
        actual = s.Poly.from_dict(terms, variables, domain=s.QQ)
        if 'generator' in step['kind']:
            assert actual == generators[step['kind']['generator']]
        else:
            expected = s.Poly(0, *variables, domain=s.QQ)
            for parent, shift, coefficient in step['parents']:
                assert parent in steps and parent < index
                assert len(shift) == len(variables) and all(e >= 0 for e in shift)
                multiplier = s.Rational(coefficient) * s.prod(
                    x**e for x, e in zip(variables, shift))
                expected += steps[parent] * s.Poly(multiplier, *variables, domain=s.QQ)
            assert actual == expected
        steps[index] = actual
    if certificate['proved_nonzero_constant']:
        constant = steps[certificate['constant_step']]
        assert constant.total_degree() == 0 and not constant.is_zero
    assert count_m == certificate['record_counts']['M']
    assert count_o == certificate['verified_output_count']
    print('PASS', name, 'M records', count_m, 'outputs', count_o,
          'verified certificate steps', len(steps),
          'nonzero constant', certificate['proved_nonzero_constant'])
print('PASS all new M rows equal their corresponding independently recorded old input rows.')
print('PASS all compact output identities independently recomputed over exact QQ.')
