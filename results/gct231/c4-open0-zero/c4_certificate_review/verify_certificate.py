"""Independent check of exported certificate DAGs; imports no author verifier."""
from fractions import Fraction as Q
from pathlib import Path
import json
import re
import hashlib
import time
import sys

BASE = Path(__file__).resolve().parent.parent

def input_polynomials(path):
    lines = path.read_text().splitlines()
    characteristic, n, count = map(int, lines[0].split())
    assert characteristic == 0
    names = lines[1].split()
    assert len(names) == n and len(set(names)) == n
    position = {name:i for i,name in enumerate(names)}
    result = []
    assert len([line for line in lines[2:] if line.strip()]) == count
    for text in lines[2:2+count]:
        # Signed flat rational monomials are the adapter's actual input format.
        chunks = re.findall(r'[+-]?[^+-]+', text)
        assert ''.join(chunks) == text
        poly = {}
        for chunk in chunks:
            sign = -1 if chunk.startswith('-') else 1
            unsigned = chunk[1:] if chunk[:1] in ('+', '-') else chunk
            factors = unsigned.split('*')
            if re.fullmatch(r'\d+(?:/\d+)?', factors[0]):
                coefficient = sign * Q(factors.pop(0))
            else:
                coefficient = Q(sign)
            exponent = [0]*n
            for factor in factors:
                pair = factor.split('^')
                assert len(pair) <= 2 and pair[0] in position
                degree = int(pair[1]) if len(pair) == 2 else 1
                assert degree >= 0
                exponent[position[pair[0]]] += degree
            key = tuple(exponent)
            poly[key] = poly.get(key,Q(0)) + coefficient
        result.append({key:value for key,value in poly.items() if value})
    return names, result

def decode(terms, n):
    out = {}
    for exponent, coefficient in terms:
        assert len(exponent) == n and all(type(x) is int and x >= 0 for x in exponent)
        key = tuple(exponent)
        assert key not in out
        value = Q(coefficient)
        assert value != 0
        out[key] = value
    return out

def check(filename):
    start = time.monotonic()
    path = BASE/filename
    data = json.loads(path.read_text())
    input_path = Path(data['input'])
    names, source = input_polynomials(input_path)
    assert names == data['variables']
    n = len(names)
    proved = {}
    dependencies = {}
    generator_count = 0
    output_count = 0
    product_terms = 0
    for step in data['steps']:
        idx = step['index']
        assert type(idx) is int and idx >= 0 and idx not in proved
        actual = decode(step['polynomial'],n)
        kind = step['kind']
        if set(kind) == {'generator'}:
            gen = kind['generator']
            assert type(gen) is int and 0 <= gen < len(source)
            assert step['parents'] == []
            assert actual == source[gen], ('wrong generator',idx,gen)
            generator_count += 1
        else:
            assert set(kind) == {'output_node'}
            reconstructed = {}
            for parent,shift,coefficient in step['parents']:
                assert parent in proved and parent < idx
                assert len(shift) == n and all(type(x) is int and x >= 0 for x in shift)
                q = Q(coefficient)
                assert q != 0
                for exponent,value in proved[parent].items():
                    target = tuple(exponent[i]+shift[i] for i in range(n))
                    reconstructed[target] = reconstructed.get(target,Q(0)) + q*value
                    product_terms += 1
            reconstructed = {key:value for key,value in reconstructed.items() if value}
            assert reconstructed == actual, ('wrong polynomial identity',idx)
            output_count += 1
        dependencies[idx] = [parent for parent,_,_ in step['parents']]
        proved[idx] = actual
    if data['proved_nonzero_constant']:
        final = data['constant_step']
        assert final in proved and set(proved[final]) == {(0,)*n}
        assert proved[final][(0,)*n] != 0
        closure = set()
        def visit(idx):
            if idx in closure:return
            closure.add(idx)
            for parent in dependencies[idx]:visit(parent)
        visit(final)
        assert closure == set(data['needed_steps'])
    else:
        assert data['constant_step'] is None
        assert not data['needed_steps']
    record = dict(file=filename, sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        input_sha256=hashlib.sha256(input_path.read_bytes()).hexdigest(),
        generators=generator_count, identities=output_count, product_terms=product_terms,
        constant=data['constant_step'], wall_seconds=time.monotonic()-start, verdict='PASS')
    print(json.dumps(record),flush=True)
    return record

if __name__ == '__main__':
    results = [check(filename) for filename in sys.argv[1:]]
    (Path(__file__).parent/'certificate-verdicts.json').write_text(json.dumps(results,indent=2)+'\n')
