from pathlib import Path
import json,struct,itertools,math,hashlib,zstandard,time,sys,resource
root=Path('/tmp/oec/pequalnp-pilot-78/numeric/s4-hadamard');start=time.monotonic();chart=json.loads((root/'chart.json').read_text());actions=json.loads(Path('/tmp/oec/pequalnp-pilot-78/construct_search/s4-hadamard-actions.json').read_text());degree=int(sys.argv[1]) if len(sys.argv)>1 else 5
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20))
polys=[{tuple(m):c for m,c in f} for f in chart['polynomials']]
def unpack(path):
 with path.open('rb') as source,zstandard.ZstdDecompressor().stream_reader(source) as reader:return reader.read()
rows=[(g,tuple(m)) for g,m in json.loads(unpack(root/f'invariant-D{degree}-rows.json.zst'))];columns=[tuple(m) for m in json.loads(unpack(root/f'invariant-D{degree}-columns.json.zst'))]
raw=unpack(root/f'invariant-D{degree}.bin.zst');nr,nc,nnz=struct.unpack_from('<IIQ',raw);assert len(raw)==16+nnz*16 and(nr,nc)==(len(rows),len(columns));matrix=[{} for _ in rows]
for n in range(nnz):
 r,c,v=struct.unpack_from('<IIq',raw,16+n*16);assert c not in matrix[r];matrix[r][c]=v

def act(m,ac):
 mapping=ac['variables'];return tuple(sorted(mapping[x][0] for x in m)),math.prod(mapping[x][1] for x in m)
def orbit(m):
 d={};negative=False
 for ac in actions:
  n,sign=act(m,ac)
  if n in d and d[n]!=sign:negative=True
  d[n]=sign
 return d,negative

def monos(d):
 for n in range(d+1):yield from itertools.combinations_with_replacement(range(18),n)
seen=set();canon=[];sizes={};neg=0
for m in monos(degree):
 if m in seen:continue
 orb,bad=orbit(m);seen.update(orb)
 if bad:neg+=1;continue
 c=min(orb);canon.append(c);sizes[c]=len(orb)
assert canon==columns
print('COLUMN_ORBITS_PASS',len(columns),'NEGATIVE_ORBITS',neg,'ALL_MONOMIALS',len(seen))
# Derive generator actions independently from raw coefficient substitution.
gactions=[]
for ac in actions:
 pairs=[]
 for f in polys:
  out={}
  for m,c in f.items():
   n,sign=act(m,ac);out[n]=out.get(n,0)+sign*c
  matches=[(i,sign) for i,g in enumerate(polys) for sign in [1,-1] if out=={m:sign*c for m,c in g.items()}]
  assert len(matches)==1;pairs.append(matches[0])
 gactions.append(pairs)
seen=set();expected=[];negative=0
for gen,exp in enumerate(chart['parameter_exponents']):
 for m in monos(degree-sum(exp)):
  pair=(gen,m)
  if pair in seen:continue
  orb={};bad=False
  for ac,gmap in zip(actions,gactions):
   n,sign=act(m,ac);gg,gsign=gmap[gen];pair2=(gg,n);sign*=gsign
   if pair2 in orb and orb[pair2]!=sign:bad=True
   orb[pair2]=sign
  seen.update(orb)
  if bad:negative+=1
  else:expected.append(min(orb))
assert expected==rows
print('ROW_ORBITS_PASS',len(rows),'NEGATIVE_ORBITS',negative,'ALL_PAIRS',len(seen))
colids={m:i for i,m in enumerate(columns)}
for r,(gen,m) in enumerate(rows):
 averaged={}
 for mon,c in polys[gen].items():
  product=tuple(sorted(m+mon))
  for ac in actions:
   target,sign=act(product,ac);averaged[target]=averaged.get(target,0)+sign*c
 expected={}
 for cmon,value in averaged.items():
  if cmon not in colids:continue
  scaled=value*sizes[cmon];assert scaled%24==0
  if scaled:expected[colids[cmon]]=scaled//24
 assert expected==matrix[r],r
print('ALL_RAW_REYNOLDS_ROWS_PASS',len(rows),'NNZ',nnz)
p=1000000007;w={}
for line in(root/f'solve-D{degree}-p1000000007.witness').read_text().splitlines():
 k,v=map(int,line.split());assert k not in w;w[k]=v
assert len(w)==nc and w[columns.index(())]==1
assert all(sum(v*w[c] for c,v in row.items())%p==0 for row in matrix)
print('DUAL_WITNESS_PASS','y_constant',1,'MODULUS',p,'ROWS',len(rows))
print('PASS','SHA256_UNCOMPRESSED',hashlib.sha256(raw).hexdigest(),'SECONDS',time.monotonic()-start)
