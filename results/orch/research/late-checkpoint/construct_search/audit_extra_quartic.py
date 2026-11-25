from pathlib import Path
import json,zstandard,math,collections,resource,time,hashlib
from fractions import Fraction
resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
start=time.monotonic(); base=Path('/tmp/oec/pequalnp-pilot-78'); out=base/'construct_search'
chart=json.loads((base/'numeric/s4-hadamard/chart.json').read_text()); actions=json.loads((out/'s4-hadamard-actions.json').read_text())
def unpack(n):
 with (base/'numeric/s4-hadamard'/n).open('rb') as f,zstandard.ZstdDecompressor().stream_reader(f) as z:return json.loads(z.read())
rows=unpack('invariant-D5-rows.json.zst'); cols=unpack('invariant-D5-columns.json.zst'); entry=json.loads((base/'numeric/s4-structure/D5-kernel-images.json').read_text())[-1]
raw=collections.defaultdict(int)
for ri,weight in entry['coefficients']:
 gen,mult=rows[ri]
 for mon,co in chart['polynomials'][gen]:
  product=mult+mon
  for ac in actions:
   mapping=ac['variables']; target=tuple(sorted(mapping[i][0] for i in product)); sign=math.prod(mapping[i][1] for i in product)
   raw[target]+=weight*co*sign
raw={m:c for m,c in raw.items() if c}
actual={m:Fraction(c,24) for m,c in raw.items()}
assert max(map(len,actual))==4
collapsed={}
for ci,c in entry['collapsed_polynomial']:
 m=tuple(cols[ci]); orbit={tuple(sorted(ac['variables'][i][0] for i in m)) for ac in actions}
 assert actual[m]*len(orbit)==c
 collapsed[ci]=c
canon=[]
for mon in actual:
 orb={tuple(sorted(ac['variables'][i][0] for i in mon)) for ac in actions}
 if mon==min(orb):canon.append(mon)
assert set(canon)=={tuple(cols[i]) for i in collapsed}
p=out/'extra-quartic-independent.json'; p.write_text(json.dumps({'source_kernel':14,'terms':[[m,c.numerator,c.denominator] for m,c in sorted(actual.items())],'identity':'sum of 76 weighted full Reynolds products / 24','degrees':dict(collections.Counter(map(len,actual)))},separators=(',',':'))+'\n')
print('EXACT_REYNOLDS_IDENTITY_PASS',len(entry['coefficients']),'ROWS',len(actual),'ACTUAL_TERMS',len(collapsed),'COLLAPSED_TERMS','DEGREES',dict(collections.Counter(map(len,actual))))
print('OUTPUT',p.name,'SHA256',hashlib.sha256(p.read_bytes()).hexdigest(),'SECONDS',time.monotonic()-start)
