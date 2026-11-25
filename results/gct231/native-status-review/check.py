from pathlib import Path
import json,hashlib,re
import sympy as s

base=Path('/workspace/pequalnp-proofs/results/gct231')
for name,count in [('native-star-r1',6),('native-b32-control',10)]:
    b=base/name;manifest=json.loads((b/'sha256.json').read_text())
    assert len(manifest)==count
    assert set(manifest)=={p.name for p in b.iterdir() if p.is_file() and p.name!='sha256.json'}
    for filename,digest in manifest.items():assert hashlib.sha256((b/filename).read_bytes()).hexdigest()==digest
    print('archive PASS',name,count,hashlib.sha256((b/'sha256.json').read_bytes()).hexdigest())
    result_path=next(b.glob('*.result.json'));result=json.loads(result_path.read_text())
    log=result_path.with_name(result_path.name.replace('.result.json','.log')).read_text()
    completed=re.findall(r'^\s*\d+\s+\d+\s+\d+\s+\d+\s+x\s+\d+\s+[\d.]+%\s+\d+ new\s+\d+ zero\s+[\d.]+\s+\|\s+[\d.]+',log,re.M)
    input_path=next(b.glob('*.in'));assert hashlib.sha256(input_path.read_bytes()).hexdigest()==result['input_sha256']
    if name=='native-star-r1':
        assert result['status']=='UNKNOWN_TIME_LIMIT' and result['returncode'] is None
        assert 600.29<result['seconds']<600.30 and result['child_maxrss_kib']==2357776
        assert len(completed)==9 and not list(b.glob('*basis.json'))
        assert log.rstrip().endswith('6    4111   14024   50436 x 117378      4.33%')
        assert result['threads']==2 and result['memory_mib']==6144 and result['cpu_soft_seconds']==1202
        print('status PASS UNKNOWN600.295s;9completedrounds;no basis;2357776KiB')
    else:
        assert result['status']=='COMPLETED' and result['returncode']==0
        assert 0.03395<result['seconds']<0.03396 and len(completed)==15
        basis_path=next(b.glob('*basis.json'));basis=json.loads(basis_path.read_text())
        assert basis=={'characteristic':1009,'nvars':9,'nterms':1,'basis':[[['1',[0]*9]]]}
        assert hashlib.sha256(basis_path.read_bytes()).hexdigest()==result['output_sha256']
        assert any(re.match(r'\s*\d+\s+33\s',row) for row in completed)
        assert any(re.match(r'\s*\d+\s+32\s',row) for row in completed)
        assert 'reduce final basis' in log
        print('status PASS F1009unit1;0.033956s;15rounds+final;selections32and33')

b=base/'native-b32-control'
raw=json.loads((b/'star-support-buchberger-equations.json').read_text())
meta=json.loads((b/'neogb-star-support-p1009.provenance.json').read_text())
assert hashlib.sha256((b/'star-support-buchberger-equations.json').read_bytes()).hexdigest()==meta['source_sha256']
names=raw['unknowns'];variables=s.symbols(' '.join(names));ns=dict(zip(names,variables))
tokens=list(map(int,(b/'neogb-star-support-p1009.in').read_text().split()))
n,m,p,total=tokens[:4];assert (n,m,p,total)==(9,31,1009,655)
lengths=tokens[4:4+m];assert sum(lengths)==total;offset=4+m
for idx,count in enumerate(lengths):
    actual={}
    for _ in range(count):
        numerator,denominator=tokens[offset:offset+2]
        exponent=tuple(tokens[offset+2:offset+2+n]);offset+=2+n
        assert denominator%p and len(exponent)==n and min(exponent)>=0 and exponent not in actual
        actual[exponent]=(numerator*pow(denominator,-1,p))%p
        assert actual[exponent]
    poly=s.Poly(s.sympify(raw['equations'][idx]['coefficient'],locals=ns),*variables,domain=s.QQ)
    scaling=meta['equation_scalings'][idx];den=int(scaling['denominator']);content=int(scaling['content'])
    assert den%p and content%p
    expected={}
    for exponent,coefficient in poly.terms():
        value=int(coefficient.p)*pow(int(coefficient.q),-1,p)*den*pow(content,-1,p)%p
        if value:expected[tuple(exponent)]=value
    assert actual==expected,idx
assert offset==len(tokens)
print('source/input PASS all31polynomials655terms;allscalingsinvertibleF1009')
