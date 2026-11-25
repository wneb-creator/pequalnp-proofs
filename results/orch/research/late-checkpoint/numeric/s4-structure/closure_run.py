from pathlib import Path
from fractions import Fraction
import collections,json,os,resource,subprocess,sys,time
OUT=Path('/tmp/oec/pequalnp-pilot-78/numeric/s4-structure');number=int(sys.argv[1]);name=f'closure-{number}'
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20));resource.setrlimit(resource.RLIMIT_CPU,(120,125));resource.setrlimit(resource.RLIMIT_FSIZE,(16*2**20,16*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
env=os.environ.copy();env['OPENBLAS_NUM_THREADS']='1';env['OMP_NUM_THREADS']='1';start=time.monotonic()
with (OUT/f'{name}.stdout').open('w') as out,(OUT/f'{name}.stderr').open('w') as err:
    try:r=subprocess.run([str(OUT/'graded-rational'),str(OUT/f'{name}-input.bin'),str(OUT/f'{name}-degrees.bin'),str(OUT/f'{name}-certificates.jsonl')],stdout=out,stderr=err,env=env,preexec_fn=limits,timeout=150);code=r.returncode
    except subprocess.TimeoutExpired:code='timeout'
report={'round':number,'exit':code,'wall_seconds':time.monotonic()-start}
if code==0:
    generators=[{tuple(m):Fraction(c) for m,c in f} for f in json.loads((OUT/f'{name}-generators.json').read_text())]
    rows=json.loads((OUT/f'{name}-rowmap.json').read_text());columns=json.loads((OUT/'rational-id-rowmap.json').read_text())['columns'];degrees=[]
    for line in (OUT/f'{name}-certificates.jsonl').read_text().splitlines():
        cert=json.loads(line);actual=collections.defaultdict(Fraction)
        for row,weight in cert['certificate']:
            g,m=rows[row];weight=Fraction(weight)
            for term,c in generators[g].items():actual[tuple(sorted(tuple(m)+term))]+=weight*c
        actual={m:c for m,c in actual.items() if c};expected={tuple(columns[c]):Fraction(v) for c,v in cert['polynomial']};assert actual==expected
        degrees.append(max(map(len,actual),default=0))
    report['certificates_verified']=len(degrees);report['degree_counts']={degree:degrees.count(degree) for degree in sorted(set(degrees))}
(OUT/f'{name}-result.json').write_text(json.dumps(report,indent=2));print(json.dumps(report),flush=True);print((OUT/f'{name}.stdout').read_text(),flush=True)
