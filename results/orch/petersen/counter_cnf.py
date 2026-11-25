"""Encode AND/OR synthesis on complete monotone critical inputs.

The generated CNF is for exploration; it does not itself certify a Lean result.
"""
import argparse
import itertools
import json
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('output')
p.add_argument('--gates',type=int,default=19)
p.add_argument('--first-symmetry',action='store_true')
p.add_argument('--top-form',action='store_true')
p.add_argument('--case',choices=['any','or-edge','or-nonedge','and-edge'],default='any')
p.add_argument('--and-min',type=int,default=0)
p.add_argument('--input-undominated',action='store_true')
p.add_argument('--ordered',action='store_true')

args=p.parse_args()
q=0
n=10
size=args.gates
critical=json.loads(Path('results/orch/petersen/counter-critical.json').read_text())
samples=critical['critical_true']+critical['critical_false']
true_count=len(critical['critical_true'])
false_indices=list(range(true_count,len(samples)))
edges={tuple(sorted(e)) for e in critical['edges']}
all_pairs=list(itertools.combinations(range(n),2))
if args.case!='any':
    extra=[1<<i for i in range(n)]+[((1<<n)-1)^(1<<i) for i in range(n)]
    extra += [(1<<i)|(1<<j) for i,j in all_pairs]
    extra += [((1<<n)-1)^(1<<i)^(1<<j) for i,j in all_pairs]
    for mask in extra:
        if mask not in samples: samples.append(mask)
sample_index={mask:s for s,mask in enumerate(samples)}
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
if args.ordered:
    # Preserve the prescribed first gate. Greedy topological order thereafter
    # sorts by (maximum predecessor, minimum predecessor, operation).
    for g in range(2,size):
        previous=n+g-1
        for a in range(previous):
            for b in range(a): clause(-right[g-1][a],-right[g][b])
        same_right,same_left=new(),new()
        for a in range(previous):
            clause(-right[g-1][a],-right[g][a],same_right)
            clause(-left[g-1][a],-left[g][a],same_left)
            for b in range(a): clause(-same_right,-left[g-1][a],-left[g][b])
        clause(-same_right,-same_left,-op[g-1],op[g])
for s,mask in enumerate(samples):
    value=any(mask&(1<<a) and mask&(1<<b) for a,b in edges)
    clause(out[-1][s] if value else -out[-1][s])
if args.and_min:
    def neg(x): return not x if isinstance(x,bool) else -x
    def logic_clause(*xs):
        if any(x is True for x in xs): return
        clause(*(x for x in xs if x is not False))
    prev=[True]+[False]*args.and_min
    for a in op:
        cur=[True]
        for j in range(1,args.and_min+1):
            t=new(); p,r=prev[j],prev[j-1]
            logic_clause(neg(p),t)
            logic_clause(-a,neg(r),t)
            logic_clause(-t,p,a)
            logic_clause(-t,p,r)
            cur.append(t)
        prev=cur
    logic_clause(prev[-1])
if args.input_undominated:
    for g in range(size):
        for i in range(n):
            beats=[]
            for s,mask in enumerate(samples[:true_count+len(false_indices)]):
                value=bool(mask&(1<<i))
                if s<true_count and not value: beats.append(out[g][s])
                if s>=true_count and value: beats.append(-out[g][s])
            clause(*beats)
if args.case!='any':
    # Three critical tests characterize equality to each raw AND/OR function.
    # These constraints forbid exact semantic equalities, not merely direct gates.
    full=(1<<n)-1
    for g in range(size):
        for i,j in all_pairs:
            if (i,j) not in edges:
                clause(-out[g][sample_index[(1<<i)|(1<<j)]],
                       out[g][sample_index[full^(1<<i)]],out[g][sample_index[full^(1<<j)]])
            forbid_or=args.case=='and-edge' or (args.case=='or-nonedge' and (i,j) in edges)
            if forbid_or:
                clause(-out[g][sample_index[1<<i]],-out[g][sample_index[1<<j]],
                       out[g][sample_index[full^(1<<i)^(1<<j)]])
        for i in range(n):
            clause(-out[g][sample_index[1<<i]],out[g][sample_index[full^(1<<i)]])
    clause(left[0][0])
    clause(right[0][2] if args.case=='or-nonedge' else right[0][1])
    clause(op[0] if args.case=='and-edge' else -op[0])
if args.top_form:
    below_and_reaches=[]
    for g in range(size):
        below,flag,fl,fr=new(),new(),new(),new()
        below_and_reaches.append(flag)
        for s in false_indices: clause(-below,-out[g][s])
        clause(below,*(out[g][s] for s in false_indices))
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
    clause(left[0][0])
    clause(right[0][1],right[0][2])
output=Path(args.output)
with output.open('w') as f:
    f.write(f'p cnf {variables} {len(clauses)}\n')
    for xs in clauses: f.write(' '.join(map(str,xs))+' 0\n')
meta=dict(q=q,n=n,gates=size,samples=samples,true_count=true_count,left=left,right=right,op=op,out=out,
          variables=variables,clauses=len(clauses),first_symmetry=args.first_symmetry,top_form=args.top_form,
          case=args.case)
meta['and_min']=args.and_min
meta['input_undominated']=args.input_undominated
meta['ordered']=args.ordered
output.with_suffix('.json').write_text(json.dumps(meta))
print(json.dumps({k:meta[k] for k in ['q','n','gates','true_count','variables','clauses','first_symmetry']}))
