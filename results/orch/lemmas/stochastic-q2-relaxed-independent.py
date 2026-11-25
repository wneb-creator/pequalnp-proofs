from pathlib import Path
from itertools import combinations_with_replacement, product
from collections import Counter
import json,time,math
N=[frozenset(i for i in range(7) if m>>i&1) for m in [11,69,98,49,88,44,22]]
required=[N[0],N[1],N[3]]
allsets=[frozenset(i for i in range(7) if m>>i&1) for m in range(128)]
Slist=[S for S in allsets if N[2]<S]
counts=Counter(); hist=Counter(); survivors=[]; start=time.monotonic()
for S in Slist:
    allowed=[U for U in allsets if len(U)<=2 or U in required or U==S]
    opts=[[A for A in required+[S] if N[i]<=A] for i in range(4)];opts[2]=[S]
    for units in combinations_with_replacement(allowed,3):
        mult=6
        for c in Counter(units).values():mult//=math.factorial(c)
        r=[frozenset(j for j,U in enumerate(units) if t in U) for t in range(7)]
        center=len(r[0])+sum(r[t]<=r[0] for t in range(1,7))
        shared=[U for U in required+[S]+list(units)]
        for A in product(*opts):
            counts['all_ordered']+=mult
            if any(sum(t in Ai for Ai in A)+(t!=0)>2+len(r[t]) for t in range(7)):continue
            counts['budget_ordered']+=mult
            if any(r[x]<=r[t] and any(x in W and t in W for W in shared) and t not in A[i] for i in range(4) for x in N[i] for t in range(7)):continue
            counts['colabel_ordered']+=mult;hist[center]+=mult
            if center<=5:
                survivors.append(dict(S=sorted(S),units=[sorted(U) for U in units],assigned=[sorted(X) for X in A],center=center))
result=dict(scope='Independent set-based exhaustive relaxed q2 census; all15 strict supersets, all21 pairs freely allowed, residual units treated as unordered multisets with exact multiplicity. Computational only.',strict_supersets=len(Slist),counts=dict(counts),center_histogram=dict(hist),survivors=survivors,seconds=time.monotonic()-start)
assert not survivors
out=Path('results/orch/lemmas/stochastic-q2-relaxed-independent.json');out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
