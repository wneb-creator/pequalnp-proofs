from pathlib import Path
import re, collections, json
root=Path('/workspace/pequalnp-proofs')
scratch=Path('/tmp/oec/pequalnp-pilot-182')
src=(root/'lean/PEqualNP/Outside/L_meta_10762.lean').read_text()
P=[int(x,16) for x in re.search(r'def rawP : List ℕ := \[(.*?)\]',src)[1].split(', ')]
row=lambda i:sum(((p>>i)&1)<<v for v,p in enumerate(P))
E=[5,10,17,18,20,33,34,40,65,68,72,96]
f=lambda x:any(x&e==e for e in E)
ind=[x for x in range(128) if not f(x) and all(f(x|1<<v) for v in range(7) if not x>>v&1)]
pairs={(e,y) for e in E for y in ind+[0]+[1<<v for v in range(7) if e>>v&1]}
pairs|={(x,x^(1<<v)) for x in range(128) if x.bit_count()==3 and f(x) for v in range(7) if x>>v&1 and not f(x^(1<<v))}
rows=[(row(i),0) for i in range(64)]
assert all(f(x) for x,y in rows)
AA=0
segs=[]
for side in [0,1]:
 groups=collections.defaultdict(list)
 for pair in sorted(pairs):groups[pair[side]].append(pair)
 sg=[]
 start=len(rows)-1
 for key,group in sorted(groups.items()):
  for pair in group:
   AA|=1<<len(rows)
   rows.append(pair)
  sg.append((start,len(rows)))
  start=len(rows)
  rows.append((0,0))
 segs.append(sg)
N=len(rows)
raw=[sum(((x>>v)&1)<<i | ((y>>v)&1)<<(N+i) for i,(x,y) in enumerate(rows)) for v in range(7)]
HX=sum(1<<b for a,b in segs[0]);HY=sum(1<<b for a,b in segs[1])
constants={'NN':str(N),'AA':hex(AA),'HX':hex(HX),'HY':hex(HY),'rawP':'['+', '.join(hex(x) for x in raw)+']','TG':hex(AA+(1<<64)-1),'segsX':repr(segs[0]),'segsY':repr(segs[1])}
for name,val in constants.items():
 src,n=re.subn(r'(^def '+name+r' : .*? := )[^\n]+',lambda m:m[1]+val,src,flags=re.M)
 assert n==1,(name,n)
src=src.replace('L_meta_10762','L_meta_10760')
(root/'results/orch/lemmas/engine_constants.json').write_text(json.dumps({'N':N,'edges':E,'independent':ind,'pairs':len(pairs),'constants':constants},indent=2))
prefix=src[:src.index('def ac0 :')]
# Pure search definitions can be compiled in this scratch module; proofs use kernel reduction later.
prefix=prefix.replace('noncomputable section','section')
for name in ['okT','okE','okS']:
 prefix=prefix.replace('noncomputable def '+name,'def '+name)
(scratch/'Engine.lean').write_text(prefix+'end PEqualNP.Outside.L_meta_10760\n')
print('Generated scratch engine',len(prefix.splitlines()),'lines; NN',N,'pairs',len(pairs))
