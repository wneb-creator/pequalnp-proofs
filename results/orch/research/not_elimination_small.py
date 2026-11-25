from itertools import combinations
from time import monotonic
import json
n=4;mask=(1<<(1<<n))-1
xs=tuple(sum(1<<j for j in range(1<<n) if j>>i&1) for i in range(n))
def mono(x):
 return all(not(x>>j&1) or x>>(j|1<<i)&1 for j in range(1<<n) for i in range(n))
all_mono={x for x in range(mask+1) if mono(x)}
def run(signed,depth):
 start=tuple(sorted(xs+((xs[0]^mask,) if signed else ())))
 front={start};best={x:0 for x in xs};time=monotonic()
 for d in range(1,depth+1):
  nxt=set()
  for state in front:
   old=set(state)
   for a,b in combinations(state,2):
    for v in (a&b,a|b):
     if v in old or v in (0,mask):continue
     if v in all_mono:best.setdefault(v,d)
     if d<depth:nxt.add(tuple(sorted((*state,v))))
  print(json.dumps(dict(signed=signed,depth=d,states=len(nxt),targets=len(best),seconds=monotonic()-time)),flush=True)
  front=nxt
 return best
a=run(False,6);b=run(True,6)
print('COUNTEREXAMPLES',[(f,a.get(f),d+1) for f,d in b.items() if f not in a or a[f]>d])
