from itertools import combinations
from time import monotonic

n=5
FULL=(1<<(1<<n))-1
xs=[sum(1<<s for s in range(1<<n) if s>>i&1) for i in range(n)]

def joinclosure(gs):
 out=[0]
 for g in gs:
  out += [x|g for x in out]
 return sorted(set(out))

def graph_of(f):
 if f&1: return None
 if any(f>>(1<<i)&1 for i in range(n)): return None
 es=[(i,j) for i in range(n) for j in range(i+1,n) if f>>((1<<i)|(1<<j))&1]
 expected=0
 for i,j in es: expected |= xs[i]&xs[j]
 return es if expected==f else None

def nofour(es):
 ad=[set() for _ in range(n)]
 for i,j in es: ad[i].add(j); ad[j].add(i)
 return all(len(ad[i]&ad[j])<=1 for i in range(n) for j in range(i+1,n))

def cover(es):
 return min(s.bit_count() for s in range(1<<n) if all((s>>i&1)or(s>>j&1) for i,j in es))

ors=joinclosure(xs)
gates1=set(a&b for a in ors for b in ors)-set(ors)
print('single AND functions',len(gates1),flush=True)
start=monotonic();found=set()
for idx,g1 in enumerate(gates1):
 os=joinclosure(xs+[g1])
 for ai,a in enumerate(os):
  for b in os[ai:]:
   g2=a&b
   for f in (g2,g1|g2):
    es=graph_of(f)
    if es is not None and nofour(es) and cover(es)>2:
     key=tuple(es)
     if key not in found:
      found.add(key);print('COUNTEREXAMPLE AND bound',es,'cover',cover(es),'g1',g1,'g2',g2,'a',a,'b',b,flush=True)
print('done',len(found),'elapsed',monotonic()-start,flush=True)
