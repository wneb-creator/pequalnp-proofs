import json
from collections import Counter
from itertools import product,combinations
from pathlib import Path
from fresh_case_charge import bits
from fresh_gadget_frontier import inputs

def setup(k,g):
 n,E,pos,neg=inputs(k,False,False,g)
 stars=[sum(1<<t for t,e in enumerate(pos) if e>>i&1) for i in range(n)]
 tabs=[]
 for z in neg:
  comps=[]
  for i in bits(((1<<n)-1)^z):
   v=stars[i];out=[]
   for p in comps:
    if p&v:v|=p
    else:out.append(p)
   comps=out+[v]
  tabs.append((z,comps))
 return len(E),stars,tabs

def rnk(k,g,depth=2):
 E,stars,tabs=setup(k,g);b=len(g);feats=[]
 for i,j in product(range(k),range(b)):
  raw=(1<<i)|(1<<(k+j));pos=stars[i]|stars[k+j]
  joins=[(t,sum(1<<u for u,c in enumerate(cs) if c&pos)) for t,(z,cs) in enumerate(tabs) if not raw&z]
  feats.append((i,j,joins))
 freq=Counter();sample=None
 for features in combinations(feats,depth):
  changes={}
  for i,j,joins in features:
   for t,a in joins:
    if a.bit_count()<2:continue
    if t not in changes:changes[t]=[a];continue
    cur=changes[t];o=[]
    for m in cur:
     if m&a:a|=m
     else:o.append(m)
    changes[t]=o+[a]
  basis={}
  for t,(z,cs) in enumerate(tabs):
   if t not in changes:ls=cs
   else:
    unseen=(1<<len(cs))-1;ls=[]
    for m in changes[t]:
     v=0
     for u in bits(m):v|=cs[u]
     ls.append(v);unseen^=m
    ls.extend(cs[u] for u in bits(unseen))
   for v in ls:
    while v:
     h=v.bit_length()-1
     if h not in basis:basis[h]=v;break
     v^=basis[h]
   if len(basis)==E:break
  val=len(basis);freq[val]+=1
  if val==min(freq):sample=[(i,j) for i,j,_ in features]
 print('E',E,'featurecount',depth,'ranks',sorted(freq.items()),'minrankexample',sample,flush=True)
if __name__=='__main__':
 r=json.loads(Path('fresh-singer-q3k7o3.json').read_text());rnk(7,r['groups'])
 r=json.loads(Path('fresh-singer-q3k8o2.json').read_text());rnk(8,r['groups'])
