"""Encode AND/OR synthesis on complete monotone critical inputs.

The generated CNF is for exploration; it does not itself certify a Lean result.
"""
import argparse
import itertools
import json
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('output')
p.add_argument('--gates',type=int,default=26)
p.add_argument('--first-symmetry',action='store_true')
p.add_argument('--top-form',action='store_true')
p.add_argument('--q',type=int,choices=[2,3],default=2)
args=p.parse_args()
q=args.q
N=q*q+q+1
n=2*N
size=args.gates
offsets=[0,1,3] if q==2 else [0,1,3,9]
lines=[sum(1<<((l+d)%N) for d in offsets) for l in range(N)]
samples=[(1<<((l+d)%N))|(1<<(N+l)) for l in range(N) for d in offsets]
true_count=len(samples)
for x in range(1<<N):
    ys=[l for l,ps in enumerate(lines) if not x&ps]
    covered=0
    for l in ys: covered|=lines[l]
    if x|covered == (1<<N)-1:
        samples.append(x|sum(1<<(N+l) for l in ys))
clauses=[]
variables=0
def new():
    global variables
    variables+=1
    return variables
def clause(*xs): clauses.append(xs)
def exactly_one(xs):
    clause(*xs)
    for x,y in itertools.combinations(xs,2): clause(-x,-y)

left=[]; right=[]; op=[]; out=[]
for g in range(size):
    available=n+g
    left.append([new() for _ in range(available)])
    right.append([new() for _ in range(available)])
    op.append(new())
    out.append([new() for _ in samples])
    exactly_one(left[g]); exactly_one(right[g])
    for a in range(available):
        for b in range(a): clause(-left[g][a],-right[g][b])
    for s,mask in enumerate(samples):
        u,v,w=new(),new(),out[g][s]
        for chosen,z in [(left[g],u),(right[g],v)]:
            for index,select in enumerate(chosen):
                if index<n:
                    clause(-select,z if mask&(1<<index) else -z)
                else:
                    old=out[index-n][s]
                    clause(-select,-z,old)
                    clause(-select,z,-old)
        a=op[g]
        clause(-a,-w,u); clause(-a,-w,v); clause(-a,w,-u,-v)
        clause(a,w,-u); clause(a,w,-v); clause(a,-w,u,v)
for s in range(len(samples)): clause(out[-1][s] if s<true_count else -out[-1][s])
if args.top_form:
    below_and_reaches=[]
    for g in range(size):
        below,flag,fl,fr=new(),new(),new(),new()
        below_and_reaches.append(flag)
        for s in range(true_count,len(samples)): clause(-below,-out[g][s])
        clause(below,*out[g][true_count:])
        for selectors,z in [(left[g],fl),(right[g],fr)]:
            for index,select in enumerate(selectors):
                if index<n: clause(-select,-z)
                else:
                    old=below_and_reaches[index-n]
                    clause(-select,-z,old)
                    clause(-select,z,-old)
        a=op[g]
        # No already-below AND can occur under another AND.
        clause(-a,-fl); clause(-a,-fr)
        # flag = fl OR fr OR (a AND below).
        clause(-fl,flag); clause(-fr,flag); clause(-a,-below,flag)
        clause(-flag,fl,fr,a); clause(-flag,fl,fr,below)
for g in range(size-1):
    clause(*(selectors[h][n+g] for h in range(g+1,size) for selectors in [left,right]))
for i in range(n):
    clause(*(selectors[g][i] for g in range(size) for selectors in [left,right]))
if args.first_symmetry:
    assert q==2
    clause(left[0][0])
    clause(right[0][1],right[0][7],right[0][8])
output=Path(args.output)
with output.open('w') as f:
    f.write(f'p cnf {variables} {len(clauses)}\n')
    for xs in clauses: f.write(' '.join(map(str,xs))+' 0\n')
meta=dict(q=q,n=n,gates=size,samples=samples,true_count=true_count,left=left,right=right,op=op,out=out,
          variables=variables,clauses=len(clauses),first_symmetry=args.first_symmetry,top_form=args.top_form)
output.with_suffix('.json').write_text(json.dumps(meta))
print(json.dumps({k:meta[k] for k in ['q','n','gates','true_count','variables','clauses','first_symmetry']}))
