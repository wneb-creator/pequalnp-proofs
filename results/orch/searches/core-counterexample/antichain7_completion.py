from itertools import combinations
from pathlib import Path
import json
base=Path('/tmp/oec/pequalnp-pilot-71/core-counterexample');source=(base/'and_free_or_sat.py').read_text();scope={};exec('class CNF:'+source.split('class CNF:',1)[1].split('n=14;k=',1)[0],scope);CNF=scope['CNF']
excluded=[[(0,1),(0,2),(1,2)],[(0,1),(0,2),(0,3)],[(0,1),(1,2),(2,3)],[(0,1),(1,2),(3,4)]]
for family,missing in enumerate(excluded):
 subsets=[set(x) for x in combinations(range(5),2) if x not in missing];m=7;n=14;c=CNF();edges=[(a,m+b) for a in range(m) for b in range(m)];ev=[c.var() for _ in edges];gvar=dict(zip(edges,ev))
 for a in range(m):c.add(gvar[a,m+a])
 for a,b in combinations(range(m),2):
  for x,y in combinations(range(m,n),2):c.add(-gvar[a,x],-gvar[a,y],-gvar[b,x],-gvar[b,y])
 clauses=[list(range(m)),list(range(m,n))]+[[i for i,U in enumerate(subsets) if t in U]+[m+i for i,U in enumerate(subsets) if t not in U] for t in range(5)]
 values=[all(any(S>>v&1 for v in clause) for clause in clauses) for S in range(1<<n)];minterms=[]
 for S,v in enumerate(values):
  if v and all(not values[S^(1<<a)] for a in range(n) if S>>a&1):
   minterms.append(S);c.add(*(x for (a,b),x in zip(edges,ev) if S>>a&1 and S>>b&1))
 stem=base/('antichain7-family'+str(family));stem.with_suffix('.cnf').write_text('p cnf '+str(c.n)+' '+str(len(c.clauses))+'\n'+'\n'.join(' '.join(map(str,cl))+' 0' for cl in c.clauses)+'\n');stem.with_suffix('.meta.json').write_text(json.dumps(dict(n=n,left=m,edges=edges,edgevars=ev,clauses=clauses,minterms=minterms,subsets=[sorted(U) for U in subsets]),indent=2));print(json.dumps(dict(family=family,variables=c.n,cnf_clauses=len(c.clauses),minterms=len(minterms))))
