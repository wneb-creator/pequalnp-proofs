from itertools import combinations
from collections import Counter
from pathlib import Path
import json
J=Path(__file__).resolve().parent;D={0,1,3,9}; sets={}; tally=Counter()
for P in combinations(range(13),5):
 ns={l:{p for p in P if (p+l)%13 in D}for l in range(13)};L=sorted(l for l,A in ns.items()if len(A)>=2); counts=tuple(sorted((len(ns[l])for l in L),reverse=True));tally[counts]+=1
 if counts in sets:continue
 E=[(i,5+j)for j,l in enumerate(L)for i,p in enumerate(P)if p in ns[l]]; free=set()
 for p in set(range(13))-set(P):
  ls=[j for j,l in enumerate(L,5)if (p+l)%13 in D]
  for k in range(2,len(ls)+1):free.update(combinations(ls,k))
 neg=[]
 for X in range(32):
  Y=set(j for i,j in E if not (X>>i&1)); Y-={j for i,j in E if X>>i&1};
  if all(X>>i&1 or any(x==i and l in Y for x,l in E) for i in range(5)):neg.append(X|sum(1<<l for l in Y))
 sets[counts]={'points':P,'lines':L,'edge_count':len(E),'E':E,'free':sorted(free),'negative_maximal':neg,'working_bound':len(E)+3,'raw_count':5+len(L),'excess_budget':len(E)+3+1-(5+len(L))}
for key,v in sets.items():print(tally[key],'sets',v['points'],key,'edges',len(v['E']),'negatives',len(v['negative_maximal']),'free',len(v['free']),'k0 excess',v['excess_budget']);
(J/'fresh-meta3773-five-point-types.json').write_text(json.dumps(list(sets.values()),indent=2)+'\n')
