from pathlib import Path
import json,functools,time
B=Path('/tmp/oec/pequalnp-pilot-10/single-not-reduction/meta1425')
TARGETS=[0xe8a8a8a8,0xe8a8e888,0xe8e8e880,0xeaa8a888,0xeaa8c888,0xeaa8e880,0xeaaac880,0xeac0e8c0,0xeac8e0c0,0xeac8e880]
CAPS=[5,6,7,8,6,8,6,5,4,8];INIT=(0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000);MASK=(1<<32)-1
allstates=allcandidates=0;start=time.monotonic()
for index,(target,cap) in enumerate(zip(TARGETS,CAPS)):
 prefix=B/f't{index}-final-tight';meta=json.loads(Path(str(prefix)+'.meta.json').read_text());assert meta['target']==target and meta['budget']==cap and meta['mode']=='tight' and tuple(meta['inputs'])==INIT
 pairs=[tuple(p) for p in json.loads((B/f't{index}-reduced-tight.pairs.json').read_text())];assert len(set(pairs))==len(pairs)
 assert all(0<=a<32 and 0<=b<32 and not(target>>a&1) and target>>b&1 for a,b in pairs)
 full=(1<<len(pairs))-1
 @functools.lru_cache(None)
 def sep(w):
  eq=direct=0
  for k,(a,b) in enumerate(pairs):
   av=w>>a&1;bv=w>>b&1
   if av!=bv:eq|=1<<k
   if not av and bv:direct|=1<<k
  return eq,direct
 def cover(ws,s,tight=True):
  flag=int(tight and len(ws)==s+1);result=0
  for w in ws:
   result|=sep(w)[flag]
   if result==full:return True
  return False
 for subset in range(31):assert not cover(tuple(INIT[j] for j in range(5) if subset>>j&1),99,False)
 layers={}
 for s in range(cap+1):
  rows=[tuple(json.loads(line))for line in Path(str(prefix)+f'.layer{s}.jsonl').read_text().splitlines()]
  assert rows==sorted(set(rows))
  for ws in rows:assert ws==tuple(sorted(ws)) and len(ws)<=s+1 and all(0<=w<=MASK for w in ws) and cover(ws,s)
  layers[s]=set(rows)
 assert layers[cap]=={INIT} and not layers[0]
 statecount=sum(map(len,layers.values()));candidates=0
 for s in range(cap,0,-1):
  found={INIT} if s-1>=4 else set()
  def check(raw):
   global candidates
   candidates+=1
   if len(raw)<=s and cover(raw,s-1):
    child=tuple(sorted(raw));assert child in layers[s-1],(index,s,raw)
    found.add(child)
  for ws in layers[s]:
   width=len(ws);slack=s+1-width
   for i in range(width):
    if slack>=1:check(ws[:i]+(ws[i]^MASK,)+ws[i+1:])
    if slack>=2:check(ws+(ws[i]^MASK,))
    for j in range(i+1,width):
     rest=ws[:i]+ws[i+1:j]+ws[j+1:]
     for value in [ws[i]&ws[j],ws[i]|ws[j]]:
      for keep in range(4):
       if keep.bit_count()>slack:continue
       check((value,)+rest+((ws[i],)if keep&1 else())+((ws[j],)if keep&2 else()))
  assert found==layers[s-1],(index,s,'unjustified source state')
 allstates+=statecount;allcandidates+=candidates
 print('PASS target',index,hex(target),'cap',cap,'states',statecount,'pairs',len(pairs),'candidates',candidates,'elapsed',round(time.monotonic()-start,2),flush=True)
assert allstates==16611
print('PASS all10 exact tight frontiers;',allstates,'states;',allcandidates,'literal successor occurrences; all selected pairs semantically valid, all proper input sublists rejected, each successor closure and next layer equality verified.')
print('Scope: independent finite computation audit, not Lean compilation or repository checker acceptance.')
