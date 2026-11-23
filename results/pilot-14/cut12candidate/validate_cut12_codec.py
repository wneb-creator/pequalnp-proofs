from pathlib import Path
import json,math,hashlib
base=Path(__file__).parent
d=json.loads((base/'Cut12CodecData.json').read_text())
m=json.loads((base/'Cut12CodecManifest.json').read_text())
payload=int(d['payload'],16); groupbits=int(d['groups'],16); offsetbits=int(d['offsets'],16); recipes=int(d['recipes'],16)
groups=[(groupbits>>(32*j))&((1<<32)-1) for j in range(d['groupcount'])]
offsets=[(offsetbits>>(16*j))&65535 for j in range(d['chunkcount']+1)]
assert offsets==sorted(offsets) and offsets[-1]==d['payloadbits']
reconstructed=[]
for j,header in enumerate(groups):
 mask=header&511;n=(header>>9)&3;start=(header>>11)&8191;firstchunk=header>>24
 end=(groups[j+1]>>11)&8191 if j+1<len(groups) else d['rowcount']
 assert start==len(reconstructed)
 width={0:1,1:10,2:18,3:25}[n]
 for c in range((end-start+31)//32):
  chunk=firstchunk+c;bits=(payload>>offsets[chunk])&((1<<(offsets[chunk+1]-offsets[chunk]))-1)
  rank=bits&((1<<width)-1);k=(bits>>width)&31;bits>>=width+5
  for t in range(min(32,end-start-32*c)):
   if t:
    q=0
    while q<7 and bits&1:q+=1;bits>>=1
    if q==7:delta=bits&((1<<width)-1);bits>>=width
    else:
     bits>>=1;delta=(q<<k)+(bits&((1<<k)-1));bits>>=k
    rank+=delta+1
   remain=rank;xs=[];upper=len(m['signals'])-10
   for arity in range(n,0,-1):
    while math.comb(upper,arity)>remain:upper-=1
    xs.append(upper+9);remain-=math.comb(upper,arity);upper-=1
   assert remain==0
   extras=list(reversed(xs));v=[x for x in range(9) if mask>>x&1]+extras
   rid=len(reconstructed);want=m['rows'][rid]
   assert (want['mask'],want['extras'],want['rank'],want['v'])==(mask,extras,rank,v),(rid,want,mask,extras,rank,v)
   reconstructed.append(v)
  assert bits==0,(chunk,bits)
assert len(reconstructed)==4734 and len({tuple(v) for v in reconstructed})==4734
for i,w in enumerate(m['signals']):
 code=(recipes>>(28*i))&((1<<28)-1);tokens=[]
 while code:tokens.append(code&15);code>>=4
 assert tokens==w['recipe'],(i,tokens,w['recipe'])
if (base/'Nonprefix12Manifest.json').exists():
 original=json.loads((base/'Nonprefix12Manifest.json').read_text())
 for old,level in zip(original['levels'],m['levels']):
  assert (old['k'],old['t'])==(level['k'],level['t'])
  assert {tuple(r['v']) for r in old['records']}=={tuple(reconstructed[i]) for i in level['rows']}
else:
 print('Original-level comparison skipped: using the frozen compressed manifest')
for name in ['Cut12CodecBody.lean','Cut12CodecData.json','Cut12CodecManifest.json']:
 raw=(base/name).read_bytes();print(name,len(raw),hashlib.sha256(raw).hexdigest())
print('PASS: all4734rows,555recipes,levelmemberships and boundedchunk consumption independently decoded')
