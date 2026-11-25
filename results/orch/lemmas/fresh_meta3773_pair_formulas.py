"""Exact bounded formula optimization on a pair of core point rows with free reusable gates.
All pure-Y OR subexpressions available in every remaining point star or in reserve B
are granted simultaneously, even though not all can coexist in a binary tree. Small
negative tests use every maximal independent set induced by these two rows and 12 Y.
"""
from pathlib import Path
import itertools,json,time
job=Path(__file__).resolve().parent
data=json.loads((job/'geometry-meta3773-core-data.json').read_text())
edges=list(map(tuple,data['edges'])); nbs=[{y for p,y in edges if p==x} for x in range(12)]; ys=set(range(12,24)); B={15,16,18}

def solve(pair):
    p,q=pair; selected={p,q}; E=[(x,y) for x,y in edges if x in selected]; tests=[{x,y} for x,y in E]
    for P in [set(),{p},{q},{p,q}]:
        tests.append(P | (ys-set.union(set(),*(nbs[x] for x in P))))
    def mask(S): return sum(1<<k for k,test in enumerate(tests) if test&S)
    target=(1<<len(E))-1
    leaves={mask({i}):str(i) for i in sorted(selected|ys)}
    for N in [B]+[nbs[x] for x in range(12) if x not in selected]:
        for size in range(2,len(N)+1):
            for subset in itertools.combinations(sorted(N),size): leaves.setdefault(mask(set(subset)), '+'.join(map(str,subset)))
    if pair in [(0,1),(0,3),(1,3)]: leaves[mask(selected)] = 'freeXpair'
    layers=[list(leaves)]; seen={k:('leaf',v) for k,v in leaves.items()}; counts=[]
    for cost in range(1,len(E)+2):
        add={}
        for i in range((cost-1)//2+1):
            for a in layers[i]:
                for b in layers[cost-i-1]:
                    v=a|b
                    if v not in seen and v not in add: add[v]=('or',a,b)
                    v=a&b
                    if v not in seen and v not in add: add[v]=('and',a,b)
        layers.append(list(add)); seen.update(add); counts.append(len(add))
        if target in seen:
            def show(v):
                r=seen[v]
                if r[0]=='leaf':return r[1]
                return '('+show(r[1])+(' | ' if r[0]=='or' else ' & ')+show(r[2])+')'
            return {'rows':pair,'edges':len(E),'usual':len(E)+1,'min_formula':cost,'formula':show(target),'counts':counts}
    raise RuntimeError(pair)
results=[solve((min(2,x),max(2,x))) for x in range(12) if x!=2]
for r in results: print(r)
(job/'fresh-meta3773-pair-formulas.json').write_text(json.dumps(results,indent=2))
