from pathlib import Path
from fractions import Fraction
import collections,hashlib,itertools,json,os,resource,struct,subprocess,time
import sympy as sp
BASE=Path('/tmp/oec/pequalnp-pilot-78');OUT=BASE/'numeric/shifted-full31';OUT.mkdir(exist_ok=True)
SOURCE=BASE/'geometry_search/tracezero_rankdrop/full31-shifted.json'
data=json.loads(SOURCE.read_text());variables=sp.symbols(' '.join(data['variables']));local=dict(zip(data['variables'],variables));polynomials=[]
for text in data['generators']:
    p=sp.Poly(sp.sympify(text,locals=local),*variables)
    polynomials.append({tuple(i for i,e in enumerate(exp)for _ in range(e)):int(c)for exp,c in p.terms()})
columns=[m for n in range(6)for m in itertools.combinations_with_replacement(range(18),n)];index={m:i for i,m in enumerate(columns)}
rows=[]
for g,f in enumerate(polynomials):
    degree=max(map(len,f));assert degree in [2,3,4]
    for n in range(6-degree):
        for m in itertools.combinations_with_replacement(range(18),n):rows.append((degree+n,g,m))
rows.sort();nnz=sum(len(polynomials[g])for _,g,m in rows)
with(OUT/'D5-input.bin').open('wb')as f:
    f.write(struct.pack('<IIQ',len(rows),len(columns),nnz))
    for r,(_,g,m)in enumerate(rows):
        for term,c in polynomials[g].items():f.write(struct.pack('<IIq',r,index[tuple(sorted(m+term))],c))
(OUT/'D5-degrees.bin').write_bytes(b''.join(struct.pack('<I',len(m))for m in columns)+b''.join(struct.pack('<I',d)for d,g,m in rows))
(OUT/'D5-rowmap.json').write_text(json.dumps({'rows':[[g,m]for _,g,m in rows],'columns':columns},separators=(',',':')))
(OUT/'generators.json').write_text(json.dumps([[[m,c]for m,c in f.items()]for f in polynomials],separators=(',',':')))
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(384*2**20,384*2**20));resource.setrlimit(resource.RLIMIT_CPU,(60,65));resource.setrlimit(resource.RLIMIT_FSIZE,(8*2**20,8*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
with(OUT/'D5.stdout').open('w')as out,(OUT/'D5.stderr').open('w')as err:
    try:r=subprocess.run([str(BASE/'numeric/s4-structure/graded-rational'),str(OUT/'D5-input.bin'),str(OUT/'D5-degrees.bin'),str(OUT/'D5-certificates.jsonl')],stdin=subprocess.DEVNULL,stdout=out,stderr=err,preexec_fn=limits,timeout=80);code=r.returncode
    except subprocess.TimeoutExpired:code='timeout'
report={'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'rows':len(rows),'columns':len(columns),'nnz':nnz,'exit':code,'seconds':time.monotonic()-start,'scope':'Exact degree-five consequences in independently audited shifted full31 chart; no complete target verdict.'}
if code==0:
    degrees=[]
    for line in(OUT/'D5-certificates.jsonl').read_text().splitlines():
        cert=json.loads(line);actual=collections.defaultdict(Fraction)
        for row,weight in cert['certificate']:
            _,g,m=rows[row];weight=Fraction(weight)
            for term,c in polynomials[g].items():actual[tuple(sorted(m+term))]+=weight*c
        actual={m:c for m,c in actual.items()if c};expected={columns[c]:Fraction(v)for c,v in cert['polynomial']};assert actual==expected
        degrees.append(max(map(len,actual),default=0))
    report['verified_certificates']=len(degrees);report['degrees']=dict(collections.Counter(degrees))
(OUT/'D5-result.json').write_text(json.dumps(report,indent=2));print(json.dumps(report),flush=True)
