from pathlib import Path
from fractions import Fraction
import collections,hashlib,itertools,json,math,struct,sys
BASE=Path('/tmp/oec/pequalnp-pilot-78/numeric');OUT=BASE/'s4-structure';round_number=int(sys.argv[1]);name=f'closure-{round_number}'
columns=json.loads((OUT/'rational-id-rowmap.json').read_text())['columns'];index={tuple(m):i for i,m in enumerate(columns)}
def normalize(poly):
    denominator=math.lcm(*(c.denominator for c in poly.values()));values={m:int(c*denominator) for m,c in poly.items() if c};divisor=math.gcd(*map(abs,values.values()));return {m:c//divisor for m,c in values.items()}
if round_number==1:
    data=json.loads((BASE/'s4-hadamard/chart.json').read_text());generators=[{tuple(m):c for m,c in f} for f in data['polynomials']]
    certificates=[json.loads(line) for line in (OUT/'graded-rational-id-certificates.jsonl').read_text().splitlines()]
else:
    prior=json.loads((OUT/f'closure-{round_number-1}-generators.json').read_text());generators=[{tuple(m):int(c) for m,c in f} for f in prior]
    certificates=[json.loads(line) for line in (OUT/f'closure-{round_number-1}-certificates.jsonl').read_text().splitlines()]
for cert in certificates:
    poly={tuple(columns[c]):Fraction(v) for c,v in cert['polynomial']};generators.append(normalize(poly))
rows=[]
for g,f in enumerate(generators):
    degree=max(map(len,f),default=0)
    if degree==0:raise RuntimeError('constant generator found; verify certificate and stop')
    for n in range(6-degree):
        for m in itertools.combinations_with_replacement(range(18),n):rows.append((degree+n,g,m))
rows.sort();nnz=sum(len(generators[g]) for _,g,m in rows)
path=OUT/f'{name}-input.bin';digest=hashlib.sha256()
with path.open('wb') as f:
    header=struct.pack('<IIQ',len(rows),len(columns),nnz);f.write(header);digest.update(header);buffer=bytearray()
    for r,(_,g,m) in enumerate(rows):
        for term,c in generators[g].items():
            assert -(2**63)<c<2**63
            col=index[tuple(sorted(m+term))];buffer.extend(struct.pack('<IIq',r,col,c))
        if len(buffer)>2**20:f.write(buffer);digest.update(buffer);buffer.clear()
    if buffer:f.write(buffer);digest.update(buffer)
(OUT/f'{name}-degrees.bin').write_bytes(b''.join(struct.pack('<I',len(m)) for m in columns)+b''.join(struct.pack('<I',degree) for degree,g,m in rows))
(OUT/f'{name}-rowmap.json').write_text(json.dumps([[g,m] for degree,g,m in rows],separators=(',',':')))
(OUT/f'{name}-generators.json').write_text(json.dumps([[[m,c] for m,c in f.items()] for f in generators],separators=(',',':')))
report={'round':round_number,'generators':len(generators),'rows':len(rows),'columns':len(columns),'nnz':nnz,'raw_bytes':path.stat().st_size,'sha256':digest.hexdigest()};(OUT/f'{name}-input.json').write_text(json.dumps(report,indent=2));print(json.dumps(report))
