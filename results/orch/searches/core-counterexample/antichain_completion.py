from itertools import combinations
from pathlib import Path
import json
source=Path('/tmp/oec/pequalnp-pilot-71/core-counterexample/and_free_or_sat.py').read_text();scope={};exec('class CNF:'+source.split('class CNF:',1)[1].split('n=14;k=',1)[0],scope);CNF=scope['CNF'];c=CNF();subsets=[set(x) for x in combinations(range(4),2)];m=6;n=12;edges=[(a,m+b) for a in range(m) for b in range(m)];ev=[c.var() for _ in edges];gvar=dict(zip(edges,ev))
for a in range(m):c.add(gvar[a,m+a])
for a,b in combinations(range(m),2):
 for x,y in combinations(range(m,n),2):c.add(-gvar[a,x],-gvar[a,y],-gvar[b,x],-gvar[b,y])
clauses=[list(range(6)),list(range(6,12))]+[[i for i,U in enumerate(subsets) if t in U]+[6+i for i,U in enumerate(subsets) if t not in U] for t in range(4)]
true_inputs=[]
for S in range(1<<n):
 if all(any(S>>v&1 for v in clause) for clause in clauses):
  true_inputs.append(S);c.add(*(v for (a,b),v in zip(edges,ev) if S>>a&1 and S>>b&1))
stem=Path('/tmp/oec/pequalnp-pilot-71/core-counterexample/antichain-completion');stem.with_suffix('.cnf').write_text('p cnf '+str(c.n)+' '+str(len(c.clauses))+'\n'+'\n'.join(' '.join(map(str,cl))+' 0' for cl in c.clauses)+'\n');stem.with_suffix('.meta.json').write_text(json.dumps(dict(n=n,left=m,edges=edges,edgevars=ev,clauses=clauses,true_inputs=true_inputs),indent=2));print(json.dumps(dict(variables=c.n,cnf_clauses=len(c.clauses),true_inputs=len(true_inputs))))
