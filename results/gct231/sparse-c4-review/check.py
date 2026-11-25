from pathlib import Path
import hashlib,json
from fractions import Fraction
import sympy as s

base=Path('/tmp/oec/pequalnp-pilot-75/gct231')
archive=Path('/workspace/pequalnp-proofs/results/gct231/sparse-c4-chart0')
manifest=json.loads((archive/'sha256.json').read_text())
print('manifest shape',type(manifest).__name__)
if isinstance(manifest,dict):
    entries=manifest
else:
    raise AssertionError('Unexpected manifest schema')
assert set(entries)=={p.name for p in archive.iterdir() if p.is_file() and p.name!='sha256.json'}
for name,digest in entries.items():
    assert hashlib.sha256((archive/name).read_bytes()).hexdigest()==digest
print('archive coverage/hash PASS',len(entries))
source=base/'fresh/c4-support-rational-chart-0.json'
input_path=base/'neogb-c4-chart0-qq.in'
raw=json.loads(source.read_text());meta=json.loads((base/'neogb-c4-chart0-qq.provenance.json').read_text())
assert hashlib.sha256(source.read_bytes()).hexdigest()==meta['source_sha256']
assert hashlib.sha256(input_path.read_bytes()).hexdigest()==meta['input_sha256']
variables=s.symbols(' '.join(raw['parameters']))
assert list(map(str,variables))==meta['variables']
lines=input_path.read_text().splitlines()
n,m,p,total=map(int,lines[0].split());lengths=list(map(int,lines[1].split()))
assert (n,m,p,total)==(6,25,0,5609)
assert len(lengths)==m and sum(lengths)==total and len(lines)==total+2
rows=[];offset=2
for length in lengths:
    row={}
    for line in lines[offset:offset+length]:
        values=list(map(int,line.split()));assert len(values)==n+2
        numerator,denominator,*exponents=values
        assert denominator!=0 and all(e>=0 for e in exponents)
        key=tuple(exponents);assert key not in row
        row[key]=Fraction(numerator,denominator)
        assert row[key]!=0
    rows.append(row);offset+=length
assert len(raw['equations'])==m
for idx,text in enumerate(raw['equations']):
    original=s.Poly(s.sympify(text,locals=dict(zip(raw['parameters'],variables))),*variables,domain=s.QQ)
    # All actual chart coefficients are primitive integral: compare directly,
    # independently of the converter's clear_denoms/primitive operations.
    exact={tuple(mon):Fraction(int(c.p),int(c.q)) for mon,c in original.terms()}
    assert exact==rows[idx],idx
    assert meta['equation_scalings'][idx]=={'denominator':'1','content':'1'}
result=json.loads((base/'neogb-c4-chart0-qq.result.json').read_text())
assert result['status']=='UNKNOWN_TIME_LIMIT' and result['returncode'] is None
assert result['wall_limit_seconds']==120 and result['seconds']>=120
assert result['input_sha256']==meta['input_sha256']
print('PASS all25 exactQQ equations,5609terms; statusUNKNOWN_TIME_LIMIT, no basis verdict')
print('source',meta['source_sha256']);print('input',meta['input_sha256'])
print('converter',hashlib.sha256((base/'neogb_convert_witt.py').read_bytes()).hexdigest())
print('manifest',hashlib.sha256((archive/'sha256.json').read_bytes()).hexdigest())
