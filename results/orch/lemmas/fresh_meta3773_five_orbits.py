"""Certify three point-set representatives using exact incidence/support signatures."""
from pathlib import Path
from itertools import combinations,permutations
from collections import Counter
import json
J=Path(__file__).resolve().parent;D={0,1,3,9}; allpts=set(range(13)); perms=list(permutations(range(5))); turn=[[sum(1<<p[i]for i in range(5)if m>>i&1) for m in range(32)]for p in perms]
def model(P):
 ns={l:sum(1<<i for i,v in enumerate(P)if (v+l)%13 in D)for l in range(13)}; ls=[l for l in range(13)if ns[l].bit_count()>=2];ors=set()
 for x in allpts-set(P):
  stars=[ns[l]for l in ls if (x+l)%13 in D];ors.update(tuple(sorted(u))for k in range(2,len(stars)+1)for u in combinations(stars,k))
 return tuple(sorted(ns[l]for l in ls)),tuple(sorted(ors))
def convert(ns,ors,p):return tuple(sorted(p[x]for x in ns)),tuple(sorted(tuple(sorted(p[m]for m in row))for row in ors))
known=json.loads((J/'fresh-meta3773-five-point-types.json').read_text());types={}
for i,r in enumerate(known):
 n,o=model(r['points']);G={convert(n,o,p) for p in turn};assert not(set(types)&G)
 for g in G:types[g]=i
count=Counter()
for P in combinations(range(13),5):count[types[model(P)]]+=1
print('Every five-point induced multi-line neighborhood family and every available pure OR map to the stated representative by a point permutation. Counts',dict(sorted(count.items())))
