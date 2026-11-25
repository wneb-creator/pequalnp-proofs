from pathlib import Path
import collections,hashlib,itertools,json,math,resource,struct,subprocess,time
import sympy as sp
BASE=Path('/tmp/oec/pequalnp-pilot-78');OUT=BASE/'numeric/rank1-macaulay';OUT.mkdir(exist_ok=True)
source=BASE/'construct_search/rank1-incident-opposite-nonzero-Q.ms';lines=source.read_text().splitlines();names=lines[0].split(',');assert lines[1]=='0';variables=sp.symbols(' '.join(names));local=dict(zip(names,variables))
polynomials=[]
for line in lines[2:]:
    if not line.strip():continue
    p=sp.Poly(sp.sympify(line.strip().rstrip(',').replace('^','**'),locals=local),*variables)
    polynomials.append({tuple(i for i,e in enumerate(exp)for _ in range(e)):int(c)for exp,c in p.terms()})
D=7;columns=[m for n in range(D+1)for m in itertools.combinations_with_replacement(range(len(variables)),n)];index={m:i for i,m in enumerate(columns)};rows=[]
for g,f in enumerate(polynomials):
    degree=max(map(len,f))
    for n in range(D+1-degree):
        for m in itertools.combinations_with_replacement(range(len(variables)),n):rows.append((degree+n,g,m))
rows.sort();nnz=sum(len(polynomials[g])for _,g,m in rows)
with(OUT/'D7-input.bin').open('wb')as f:
    f.write(struct.pack('<IIQ',len(rows),len(columns),nnz));buffer=bytearray()
    for r,(_,g,m)in enumerate(rows):
        for term,c in polynomials[g].items():buffer.extend(struct.pack('<IIq',r,index[tuple(sorted(m+term))],c))
        if len(buffer)>2**20:f.write(buffer);buffer.clear()
    if buffer:f.write(buffer)
(OUT/'D7-degrees.bin').write_bytes(b''.join(struct.pack('<I',len(m))for m in columns)+b''.join(struct.pack('<I',d)for d,g,m in rows))
(OUT/'D7-rowmap.json').write_text(json.dumps({'variables':names,'rows':[[g,m]for d,g,m in rows],'columns':columns},separators=(',',':')))
(OUT/'generators.json').write_text(json.dumps([[[m,c]for m,c in f.items()]for f in polynomials],separators=(',',':')))
original=(BASE/'numeric/s4-structure/graded-sparse.cpp').read_text();needle='degree[order[col]]<=4';assert original.count(needle)==1;modified=original.replace(needle,'degree[order[col]]==0');(OUT/'graded-constant-mod.cpp').write_text(modified)
with(OUT/'compile.stdout').open('w')as out,(OUT/'compile.stderr').open('w')as err:subprocess.run(['c++','-O3','-std=c++17',str(OUT/'graded-constant-mod.cpp'),'-o',str(OUT/'graded-constant-mod')],stdout=out,stderr=err,check=True)
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(384*2**20,384*2**20));resource.setrlimit(resource.RLIMIT_CPU,(60,65));resource.setrlimit(resource.RLIMIT_FSIZE,(2**20,2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
with(OUT/'D7-mod.stdout').open('w')as out,(OUT/'D7-mod.stderr').open('w')as err:
    try:r=subprocess.run([str(OUT/'graded-constant-mod'),str(OUT/'D7-input.bin'),str(OUT/'D7-degrees.bin'),str(OUT/'D7-mod-constant.jsonl')],stdin=subprocess.DEVNULL,stdout=out,stderr=err,preexec_fn=limits,timeout=80);code=r.returncode
    except subprocess.TimeoutExpired:code='timeout'
report={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'degree':D,'rows':len(rows),'columns':len(columns),'nnz':nnz,'exit':code,'wall_seconds':time.monotonic()-start,'scope':'Bounded degree7 constant-membership diagnostic over F1000000007 only; no characteristic-zero certificate.'}
if code==0:report['constant_rows']=[json.loads(s)for s in(OUT/'D7-mod-constant.jsonl').read_text().splitlines()]
(OUT/'D7-mod-result.json').write_text(json.dumps(report,indent=2));print(json.dumps(report),flush=True)
