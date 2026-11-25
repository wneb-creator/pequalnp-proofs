import json
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-62')
d=json.loads((p/'packing3-blocks.json').read_text())
blocks=d['blocks']; nodes=0

def ok(s,b): return not(s[0]&b[0]) and not(s[4]&b[1])
def step(s,b):
 return (s[0]|b[0],s[1]|b[2],s[2]|b[1],s[3]|(s[2]&b[1]),s[4]|(s[3]&b[1]),s[5]+1)
def check(fuel,s,bs):
 global nodes
 nodes+=1
 upper=s[1]
 for b in bs: upper|=b[2]
 if upper.bit_count()<=29+s[5]: return True
 if s[1].bit_count()>29+s[5]: return False
 if not fuel: return not bs
 for i,b in enumerate(bs):
  if not ok(s,b): continue
  t=step(s,b)
  if not check(fuel-1,t,[c for c in bs[i+1:] if ok(t,c)]): return False
 return True
s=(0,0,0,0,0,0)
for i in d['root_indices'][21]: s=step(s,blocks[i])
assert check(26,s,[b for b in blocks if ok(s,b)])
print('root21 true; DFSnodes',nodes)
assert nodes==811
assert all(vertices==((1<<u)|(1<<v)) for (u,v),(vertices,_,_) in zip(d['coords'],blocks))
assert all(active==sum(1<<r for r,row in enumerate(d['rows']) if row&vertices) for vertices,active,_ in blocks)
assert all(edge==sum(1<<e for e,mask in enumerate(d['edges']) if mask&vertices) for vertices,_,edge in blocks)
print('All351 literal Block masks match26coordinates,468rows,52Flags-ordered edges')
