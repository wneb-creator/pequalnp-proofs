"""Exact exploration: six-cycle with three supplied opposite-pair OR wires."""
import itertools
import json
from pathlib import Path
import sys

output=Path(sys.argv[1])
size=int(sys.argv[2]) if len(sys.argv)>2 else 7
n=9
samples=[]
desired=[]
for raw in range(64):
    mask=raw
    for i in range(3):
        if raw&(1<<i) or raw&(1<<(i+3)): mask|=1<<(i+6)
    samples.append(mask)
    desired.append(any(raw&(1<<i) and raw&(1<<(j+3)) for i in range(3) for j in range(3) if i!=j))
clauses=[]; variables=0
def new():
    global variables
    variables+=1
    return variables
def clause(*xs): clauses.append(xs)
def exactly_one(xs):
    clause(*xs)
    for x,y in itertools.combinations(xs,2): clause(-x,-y)
left=[];right=[];op=[];out=[]
for g in range(size):
    available=n+g
    left.append([new() for _ in range(available)])
    right.append([new() for _ in range(available)])
    op.append(new());out.append([new() for _ in samples])
    exactly_one(left[g]);exactly_one(right[g])
    for a in range(available):
        for b in range(a): clause(-left[g][a],-right[g][b])
    for s,mask in enumerate(samples):
        u,v,w=new(),new(),out[g][s]
        for selectors,z in [(left[g],u),(right[g],v)]:
            for index,select in enumerate(selectors):
                if index<n: clause(-select,z if mask&(1<<index) else -z)
                else:
                    previous=out[index-n][s]
                    clause(-select,-z,previous);clause(-select,z,-previous)
        a=op[g]
        clause(-a,-w,u);clause(-a,-w,v);clause(-a,w,-u,-v)
        clause(a,w,-u);clause(a,w,-v);clause(a,-w,u,v)
for s,value in enumerate(desired): clause(out[-1][s] if value else -out[-1][s])
for g in range(size-1):
    clause(*(selectors[h][n+g] for h in range(g+1,size) for selectors in [left,right]))
with output.open('w') as f:
    f.write(f'p cnf {variables} {len(clauses)}\n')
    for xs in clauses:f.write(' '.join(map(str,xs))+' 0\n')
meta=dict(n=n,gates=size,left=left,right=right,op=op,out=out,samples=samples,desired=desired,
          variables=variables,clauses=len(clauses))
output.with_suffix('.json').write_text(json.dumps(meta))
print(json.dumps({k:meta[k] for k in ['n','gates','variables','clauses']}))
