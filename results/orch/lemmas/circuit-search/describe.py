import json,itertools,sys
from pathlib import Path
D={0,1,3,9}
def target(mask):return any((mask>>p&1) and(mask>>(13+l)&1) for p in range(13) for l in range(13) if(p+l)%13 in D)
def describe(g):
    falsemins=[];counts=[]
    for size in range(1,4):
        this=[]
        for c in itertools.combinations(range(26),size):
            mask=sum(1<<i for i in c)
            if target(mask) or any((old&mask)==old for old in falsemins):continue
            vs=[bool(mask>>i&1) for i in range(26)]
            for op,a,b in g:vs.append((vs[a] or vs[b]) if op else(vs[a] and vs[b]))
            if vs[-1]:this.append(mask)
        falsemins.extend(this);counts.append(len(this))
    return {'false_minimal_support_counts_size1to3':counts,'examples':[tuple(i for i in range(26) if mask>>i&1) for mask in falsemins[:12]]}
for arg in sys.argv[1:]:
    p=Path(arg);print(p.name,json.dumps(describe(json.loads(p.read_text()))))
