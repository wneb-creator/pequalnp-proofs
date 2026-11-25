"""Permute full-star coefficient variables into the three basis-direction groups."""
import argparse
import hashlib
import json
from pathlib import Path
import sympy as s

parser=argparse.ArgumentParser()
parser.add_argument('source',type=Path)
parser.add_argument('output',type=Path)
args=parser.parse_args()
data=json.loads(args.source.read_text())
old=data['unknowns']
groups=[[f'd{i}' for i in range(offset,9,3)]+[f'o{i}' for i in range(offset,9,3)]
        for offset in range(3)]
new=sum(groups,[])
assert len(old)==len(new)==18 and set(old)==set(new)
assert len(data['equations'])==31
variables=s.symbols(new)
namespace=dict(zip(new,variables))
counts=[0,0,0]
for equation in data['equations']:
    z_degree=equation['monomial'][2]
    polynomial=s.Poly(s.sympify(equation['coefficient'],locals=namespace),
                      *variables,domain=s.QQ)
    assert all(sum(exponents[12:])<=z_degree for exponents,_ in polynomial.terms())
    counts[min(z_degree,2)]+=1
assert counts==[12,9,10]
data['unknowns']=new
data['basis_direction_groups']=groups
data['reordered_from_sha256']=hashlib.sha256(args.source.read_bytes()).hexdigest()
data['scope']='Same full31 equations; ordinary DRL variable order grouped by basis direction A,B,C.'
args.output.write_text(json.dumps(data,indent=2)+'\n')
print('PASS exact variable permutation; all31 coefficient strings unchanged.')
print('Groups:',groups)
print('z-degree0/1/at-least2 equation counts:',counts)
print('Source SHA256:',data['reordered_from_sha256'])
print('Reordered SHA256:',hashlib.sha256(args.output.read_bytes()).hexdigest())
