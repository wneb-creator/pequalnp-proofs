"""Convert a rational Witt-chart equation list to exact neogb sparse input."""
import argparse
import hashlib
import json
from pathlib import Path
import sympy as s

parser = argparse.ArgumentParser()
parser.add_argument('source', type=Path)
parser.add_argument('output', type=Path)
parser.add_argument('--characteristic', type=int, default=0)
args = parser.parse_args()
assert args.characteristic == 0 or s.isprime(args.characteristic)
data = json.loads(args.source.read_text())
assert set(data) == {'parameters', 'equations'}
names = data['parameters']
variables = s.symbols(names)
namespace = dict(zip(names, variables))
rows, lengths, scalings = [], [], []
for text in data['equations']:
    polynomial = s.Poly(s.sympify(text, locals=namespace), *variables, domain=s.QQ)
    denominator, integer = polynomial.clear_denoms()
    content, primitive = integer.primitive()
    if primitive.is_zero:
        continue
    if args.characteristic:
        assert int(denominator) % args.characteristic != 0
        assert int(content) % args.characteristic != 0
    terms = [(int(coefficient), tuple(exponents))
             for exponents, coefficient in primitive.terms()
             if not args.characteristic or int(coefficient) % args.characteristic != 0]
    assert terms
    lengths.append(len(terms))
    rows.extend(terms)
    scalings.append({'denominator': str(denominator), 'content': str(content)})
output = f'{len(names)} {len(lengths)} {args.characteristic} {len(rows)}\n'
output += ' '.join(map(str, lengths)) + '\n'
output += ''.join(f'{coefficient} 1 ' + ' '.join(map(str, exponents)) + '\n'
                  for coefficient, exponents in rows)
args.output.write_text(output)
meta = {'source': str(args.source),
        'source_sha256': hashlib.sha256(args.source.read_bytes()).hexdigest(),
        'variables': names, 'characteristic': args.characteristic,
        'generator_count': len(lengths), 'term_count': len(rows),
        'equation_scalings': scalings,
        'input_sha256': hashlib.sha256(args.output.read_bytes()).hexdigest()}
args.output.with_suffix('.provenance.json').write_text(json.dumps(meta, indent=2) + '\n')
print(json.dumps({key: value for key, value in meta.items()
                 if key not in ('variables', 'equation_scalings')}, sort_keys=True))
