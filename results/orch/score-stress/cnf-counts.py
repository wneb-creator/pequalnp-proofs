from itertools import product

def count(label,p,q,edges):
 N=[sum(1<<b for a,b in edges if a==i) for i in range(p)]
 maximal=[]
 for A in range(1<<p):
  NA=0
  for i in range(p):
   if A>>i&1:NA|=N[i]
  B=((1<<q)-1)^NA
  if all((A>>i&1) or N[i]&B for i in range(p)):maximal.append(A|(B<<p))
 print(label,'maximal_false',len(maximal),'E+tau',len(edges)+p,'complete_CNF_score_lower_bound',2*len(maximal))

pairs=[(a,b) for a in range(4) for b in range(a+1,4)]
count('k4-incidence',4,6,[(v,i) for i,ab in enumerate(pairs) for v in ab])
for prime in [2,3]:
 vs=[v for v in product(range(prime),repeat=3) if any(v) and next(x for x in v if x)==1]
 p=len(vs)
 edges=[(i,j) for i,a in enumerate(vs) for j,b in enumerate(vs) if sum(x*y for x,y in zip(a,b))%prime==0]
 count('PG(2,%d)'%prime,p,p,edges)
