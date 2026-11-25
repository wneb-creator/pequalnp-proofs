from pathlib import Path
import hashlib,itertools,json,math,random,resource,shutil,struct,sys,time,zstandard
DATA=Path('/tmp/oec/pequalnp-pilot-78/numeric/s4-hadamard')
group=sys.argv[1];assert group in ('id','sign','s3','s3sign','d8')
OUT=Path('/tmp/oec/pequalnp-pilot-78/numeric/s4-structure')/('block-'+group);OUT.mkdir(exist_ok=True)
degree=int(sys.argv[2]);assert degree==5
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(240,245))
start=time.monotonic()
data=json.loads((DATA/'chart.json').read_text())
polys=[{tuple(m):c for m,c in f} for f in data['polynomials']]
actions=data['actions']
if group=='id':actions=[a for a in actions if a['permutation']==[0,1,2,3]]
if group.startswith('s3'):actions=[a for a in actions if a['permutation'][0]==0]
if group=='d8':actions=[a for a in actions if {frozenset(a['permutation'][i] for i in (0,1)),frozenset(a['permutation'][i] for i in (2,3))}=={frozenset((0,1)),frozenset((2,3))}]
def parity(perm):return (-1)**sum(perm[i]>perm[j] for i in range(4) for j in range(i+1,4))
characters=[parity(a['permutation']) if group in ('sign','s3sign') else 1 for a in actions]
size=len(actions);assert size==({'id':1,'sign':24,'s3':6,'s3sign':6,'d8':8}[group])
gdegrees=[sum(x) for x in data['parameter_exponents']]
def monomials(d):
    for n in range(d+1):yield from itertools.combinations_with_replacement(range(18),n)
def encode(m):
    value=0
    for v in m:value=(value<<5)|(v+1)
    return value
def action(m,g):
    a=actions[g]['variables']
    return tuple(sorted(a[v][0] for v in m)),characters[g]*math.prod(a[v][1] for v in m)
column_index={};columns=[];orbit_sizes=[];negative_columns=0
for m in monomials(degree):
    if encode(m) in column_index:continue
    orbit={}
    valid=True
    for g in range(size):
        n,sign=action(m,g)
        if n in orbit and orbit[n]!=sign:valid=False
        orbit[n]=sign
    if not valid:
        negative_columns+=1
        for n in orbit:column_index[encode(n)]=0
        continue
    canonical=min(orbit);orientation=orbit[canonical];index=len(columns)
    columns.append(canonical);orbit_sizes.append(len(orbit))
    positive=index+1;negative=-positive
    for n,sign in orbit.items():column_index[encode(n)]=positive if sign*orientation==1 else negative
constant=column_index[0]-1
print(json.dumps({'phase':'columns','degree':degree,'columns':len(columns),'negative_orbits':negative_columns,'all_monomials':len(column_index),'seconds':time.monotonic()-start}),flush=True)
rows=[];seen=set();negative_rows=0
small={d:list(monomials(d)) for d in set(degree-d for d in gdegrees)}
for generator in range(31):
    for m in small[degree-gdegrees[generator]]:
        candidate=32*encode(m)+generator
        if candidate in seen:continue
        orbit={};valid=True
        for g in range(size):
            n,sign=action(m,g);target=actions[g]['generatormap'][generator]
            sign*=actions[g]['generatorsign'][generator]
            pair=(target,n)
            if pair in orbit and orbit[pair]!=sign:valid=False
            orbit[pair]=sign
        seen.update(32*encode(n)+g for g,n in orbit)
        if valid:rows.append(min(orbit))
        else:negative_rows+=1
del seen,small
print(json.dumps({'phase':'rows','degree':degree,'rows':len(rows),'negative_orbits':negative_rows,'seconds':time.monotonic()-start}),flush=True)
def row_product(generator,m):
    result={}
    for term,c in polys[generator].items():
        code=column_index[encode(tuple(sorted(m+term)))]
        if code:
            column=abs(code)-1;sign=1 if code>0 else -1
            result[column]=result.get(column,0)+sign*c
    return {j:c for j,c in result.items() if c}
validation=[]
for r in random.Random(231+degree).sample(range(len(rows)),min(12,len(rows))):
    gen,m=rows[r];expected=row_product(gen,m);explicit={}
    for g in range(size):
        mm,sign=action(m,g);gg=actions[g]['generatormap'][gen]
        sign*=actions[g]['generatorsign'][gen]
        for term,c in polys[gg].items():
            target=tuple(sorted(mm+term));explicit[target]=explicit.get(target,0)+sign*c
    collapsed={}
    for term,c in explicit.items():
        if not c:continue
        code=column_index[encode(term)];assert code
        col=abs(code)-1;sign=1 if code>0 else -1
        collapsed[col]=collapsed.get(col,0)+sign*c
        assert c*sign*orbit_sizes[col]==size*expected[col]
    collapsed={j:c for j,c in collapsed.items() if c}
    assert collapsed=={j:size*c for j,c in expected.items()}
    validation.append(r)
sizes=[];nnz=0;maximum=0
for gen,m in rows:
    values=row_product(gen,m);sizes.append(len(values));nnz+=len(values)
    maximum=max(maximum,max(map(abs,values.values()),default=0))
print(json.dumps({'phase':'counted','nnz':nnz,'maximum':maximum,'raw_bytes':16+16*nnz,'seconds':time.monotonic()-start}),flush=True)
name=f'invariant-D{degree}'
path=OUT/f'{name}.bin.zst';digest=hashlib.sha256();raw_size=0
with path.open('wb') as dst,zstandard.ZstdCompressor(level=3).stream_writer(dst,closefd=False) as compressed:
    header=struct.pack('<IIQ',len(rows),len(columns),nnz);compressed.write(header);digest.update(header);raw_size+=len(header)
    buffer=bytearray()
    for r,(gen,m) in enumerate(rows):
        values=row_product(gen,m);assert len(values)==sizes[r]
        for col,c in sorted(values.items()):buffer.extend(struct.pack('<IIq',r,col,c))
        if len(buffer)>2**20:
            compressed.write(buffer);digest.update(buffer);raw_size+=len(buffer);buffer.clear()
    if buffer:compressed.write(buffer);digest.update(buffer);raw_size+=len(buffer)
assert raw_size==16+16*nnz
verify=hashlib.sha256()
with path.open('rb') as src,zstandard.ZstdDecompressor().stream_reader(src) as stream:
    while chunk:=stream.read(2**20):verify.update(chunk)
assert verify.digest()==digest.digest()
for kind,value in [('rows',rows),('columns',columns)]:
    raw=json.dumps(value,separators=(',',':')).encode();packed=zstandard.ZstdCompressor(level=3).compress(raw)
    assert zstandard.ZstdDecompressor().decompress(packed)==raw
    (OUT/f'{name}-{kind}.json.zst').write_bytes(packed)
report={'pass':True,'degree':degree,'rows':len(rows),'columns':len(columns),'nnz':nnz,'constant_column':constant,'maximum_abs_coefficient':maximum,'binary_uncompressed_sha256':digest.hexdigest(),'binary_compressed_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'raw_bytes':raw_size,'compressed_bytes':path.stat().st_size,'averaging_rows_checked':validation,'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'disk_free':shutil.disk_usage(OUT).free,'scope':'exact signed-orbit coinvariant matrix with Reynolds-average validation; no solve'}
(OUT/f'{name}-validation.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report),flush=True)
