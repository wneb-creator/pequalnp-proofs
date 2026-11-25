from pathlib import Path
from collections import Counter
from fractions import Fraction
import json,hashlib,re,math
import sympy as s

base=Path('/workspace/pequalnp-proofs/results/gct231')
scratch=Path('/tmp/oec/pequalnp-pilot-75/gct231')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for name,count in [('native-star-b32-r2',7),('native-c4-qc',17)]:
    b=base/name;manifest=json.loads((b/'sha256.json').read_text())
    assert len(manifest)==count
    assert set(manifest)=={p.name for p in b.iterdir() if p.is_file() and p.name!='sha256.json'}
    for filename,h in manifest.items():assert digest(b/filename)==h
    print('archive PASS',name,count,digest(b/'sha256.json'))
    rp=next(b.glob('*.result.json'));result=json.loads(rp.read_text())
    log=rp.with_name(rp.name.replace('.result.json','.log')).read_text()
    rounds=re.findall(r'^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+x\s+(\d+)\s+([\d.]+)%\s+(\d+) new\s+(\d+) zero\s+([\d.]+)\s+\|\s+([\d.]+)',log,re.M)
    ip=next(b.glob('*.in'));assert digest(ip)==result['input_sha256']
    launch=json.loads(next(b.glob('*.launch.json')).read_text())
    assert launch['files']['input']['sha256']==digest(ip)
    assert launch['files']['wrapper']['sha256']==digest(b/'run_neogb_native.py')
    for key in ('binary','library'):assert launch['files'][key]['sha256']==result[key+'_sha256']
    if name=='native-star-b32-r2':
        assert result['status']=='UNKNOWN_TIME_LIMIT' and result['returncode'] is None
        assert 600.085<result['seconds']<600.086 and result['child_maxrss_kib']==1645844
        assert len(rounds)==126 and not list(b.glob('*basis.json'))
        assert rounds[-1][0]=='6' and rounds[-1][1]=='33' and rounds[-1][6:9]==('28','5','16.30')
        assert max(int(row[1]) for row in rounds)==35
        assert result['threads']==2 and result['memory_mib']==6144
        assert ip.read_bytes()==(base/'native-star-r1/neogb-star-full-p1009.in').read_bytes()
        print('status PASS UNKNOWN600.085s;126completedrounds;no basis;input unchanged')
    else:
        assert result['status']=='COMPLETED' and result['returncode']==0
        assert 17.229<result['seconds']<17.230 and result['child_maxrss_kib']==81300
        assert len(rounds)==144 and 'reduce final basis' in log
        bp=next(b.glob('*basis.json'));basis=json.loads(bp.read_text())
        assert basis=={'characteristic':1009,'nvars':12,'nterms':1,'basis':[[['1',[0]*12]]]}
        assert digest(bp)==result['output_sha256']
        assert result['threads']==1 and result['memory_mib']==4096
        print('status PASS modular[1];17.229s;144pairrounds+finalreduction;notQQcertificate')

b=base/'native-c4-qc'
full=json.loads((b/'path-c4-equations.json').read_text())
subset=json.loads((b/'path-c4-qc-equations.json').read_text())
selected=[record for record in full['equations'] if sum(record['monomial']) in (2,3)]
assert subset['equations']==selected
assert len(selected)==16 and Counter(sum(e['monomial']) for e in selected)=={2:6,3:10}
assert len({tuple(e['monomial']) for e in selected})==16
assert subset['subset_source_sha256']==digest(b/'path-c4-equations.json')
for key,value in full.items():
    if key not in ('equations','scope'):assert subset[key]==value
print('selection PASS exact ordered6quadratic+10cubic subset; other chart data unchanged')

meta=json.loads((b/'neogb-path-c4-qc-p1009.provenance.json').read_text())
ip=b/'neogb-path-c4-qc-p1009.in'
assert meta['source_sha256']==digest(b/'path-c4-qc-equations.json') and meta['input_sha256']==digest(ip)
names=subset['unknowns'];assert names==meta['variables']
variables=s.symbols(' '.join(names));ns=dict(zip(names,variables))
tokens=list(map(int,ip.read_text().split()));n,m,p,total=tokens[:4]
assert (n,m,p,total)==(12,16,1009,492)
lengths=tokens[4:4+m];assert sum(lengths)==total;offset=4+m
for idx,count in enumerate(lengths):
    actual={}
    for _ in range(count):
        numerator,denominator=tokens[offset:offset+2]
        exponent=tuple(tokens[offset+2:offset+2+n]);offset+=2+n
        assert denominator==1 and len(exponent)==n and min(exponent)>=0 and exponent not in actual
        actual[exponent]=Fraction(numerator,denominator);assert actual[exponent] and numerator%p
    poly=s.Poly(s.sympify(selected[idx]['coefficient'],locals=ns),*variables,domain=s.QQ)
    den=math.lcm(*(int(c.q) for c in poly.coeffs()))
    content=math.gcd(*(abs(int(c*den)) for c in poly.coeffs()))
    assert den>0 and content>0 and den%p and content%p
    assert meta['equation_scalings'][idx]=={'denominator':str(den),'content':str(content)}
    expected={tuple(mon):Fraction(int(c.p),int(c.q))*den/content for mon,c in poly.terms()}
    assert actual==expected,idx
assert offset==len(tokens) and meta['dropped_modular_zero_terms']==0
print('input PASS all16 exact primitiveQQ rows/492terms; hence equalF1009; invertible scalings')
qq=scratch/'sparse-engine/certificate-trace-compact/path-c4-qc.in'
lhs=ip.read_text().splitlines();rhs=qq.read_text().splitlines()
assert lhs[1:]==rhs[1:] and lhs[0]=='12 16 1009 492' and rhs[0]=='12 16 0 492'
assert digest(qq)=='0fa4cd49e431d0a087b57b4d5961ff8e85240dec6e39369998d9544a6b0b809b'
print('crosscheck PASS QQ input body byte-identical; only characteristic differs')
print('PASS no solver rerun, no claim of characteristic-zero inconsistency')
