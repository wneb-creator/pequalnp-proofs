from itertools import combinations,permutations
import json
from pathlib import Path
V=[2,0,1,3,13,25,14,15]
P=sorted([(1<<i)|(1<<j) for i in range(8) for j in range(i+1,8)
    if (V[i]<13<=V[j] and (V[i]-V[j]+13)%13 in (0,1,3,9)) or
       (V[j]<13<=V[i] and (V[j]-V[i]+13)%13 in (0,1,3,9))])
# Match the solver's global point/line enumeration.
P=sorted(P,key=lambda m:tuple(sorted(V[i] for i in range(8) if m>>i&1)))
posidx={v:i for i,v in enumerate(P)}
stars=[sum((m>>i&1)<<j for j,m in enumerate(P)) for i in range(8)]
forms=sorted(set(stars+[1<<i for i in range(9)]))
actions=[]
negative=set(json.loads(Path('/tmp/oec/pequalnp-pilot-62/theta-truth.json').read_text())['maximal_negative_masks'])
for perm in permutations(range(3)):
 for dual in (False,True):
    f=[0,1+perm[0],1+perm[1],1+perm[2],4,5+perm[0],5+perm[1],5+perm[2]]
    if dual:
      d=[4,5,6,7,0,1,2,3];f=[d[v] for v in f]
    assert {sum(1<<f[i] for i in range(8) if m>>i&1) for m in negative}==negative
    actions.append([posidx[sum(1<<f[i] for i in range(8) if m>>i&1)] for m in P])
def act(sig,a):return sum(1<<a[i] for i in range(9) if sig>>i&1)
def canon(pair):return min(tuple(sorted(act(s,a) for s in pair)) for a in actions)
orbits={}
for a,b in combinations(forms,2):
 if a&~b and b&~a:
  orbits.setdefault(canon((a,b)),[]).append((a,b))
D={'positive_masks':P,'input_signatures':stars,'orbits':[{'representative':list(k),'size':len(v)} for k,v in sorted(orbits.items())]}
Path('/tmp/oec/pequalnp-pilot-62/theta-orbits.json').write_text(json.dumps(D,indent=2)+'\n')
print(json.dumps(D,indent=2))
