from itertools import combinations
from time import monotonic
n=5
FULL=(1<<(1<<n))-1
xs=[sum(1<<s for s in range(1<<n) if s>>i&1) for i in range(n)]
esall=list(combinations(range(n),2))
def meetclosure(gs):
 out=[FULL]
 for g in gs: out += [x&g for x in out]
 return sorted(set(out))
def nofour(es):
 ad=[set() for _ in range(n)]
 for i,j in es: ad[i].add(j);ad[j].add(i)
 return all(len(ad[i]&ad[j])<=1 for i in range(n) for j in range(i+1,n))
target={}
for m in range(1<<len(esall)):
 es=[e for i,e in enumerate(esall) if m>>i&1]
 if len(es)<4 or not nofour(es): continue
 f=0
 for i,j in es:f |= xs[i]&xs[j]
 target[f]=es
ands=meetclosure(xs)
gates1=set(a|b for a in ands for b in ands)-set(ands)
print('single OR functions',len(gates1),'targets',len(target),flush=True)
start=monotonic();found=set()
for g1 in gates1:
 os=meetclosure(xs+[g1])
 finals=meetclosure(xs+[g1])
 for ai,a in enumerate(os):
  for b in os[ai:]:
   g2=a|b
   for h in finals:
    f=g2&h
    if f in target and f not in found:
     found.add(f);print('COUNTEREXAMPLE OR bound',target[f],'g1',g1,'g2',g2,'a',a,'b',b,'finalAnd',h,flush=True)
print('done',len(found),'elapsed',monotonic()-start,flush=True)
