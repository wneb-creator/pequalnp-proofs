"""Emit exact selector-based CNF for monotone circuits with free OR gates.

The normalization constraints use the singleton-stripping theorem L_meta_563:
bare variable sets on the two sides of an AND gate can be made disjoint.
No solver result from this script is a Lean proof.
"""
import argparse, itertools, json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--mode', choices=['fooling','plane'], required=True)
parser.add_argument('--side', type=int, default=4)
parser.add_argument('--ands', type=int, required=True)
parser.add_argument('--prefix', required=True)
parser.add_argument('--row-cuts', action='store_true')
parser.add_argument('--side-order', action='store_true')
parser.add_argument('--positive-use', action='store_true')
parser.add_argument('--anchor-flag', action='store_true')
args = parser.parse_args()
k = args.ands
n = 26 if args.mode == 'plane' else 2*args.side
clauses = []
nv = 0
def fresh():
    global nv
    nv += 1
    return nv
def clause(*lits):
    clauses.append(list(lits))
def conjunction(a,b):
    c=fresh()
    clause(-c,a);clause(-c,b);clause(c,-a,-b)
    return c
def disjunction(xs):
    c=fresh()
    for a in xs:clause(-a,c)
    clause(-c,*xs)
    return c
def at_most(xs, bound):
    if bound < 0:
        clause()
        return
    if bound >= len(xs):return
    previous=[]
    for i,x in enumerate(xs):
        current=[fresh() for _ in range(min(i+1,bound+1))]
        clause(-x,current[0])
        for j,s in enumerate(previous):
            clause(-s,current[j])
            if j+1<len(current):clause(-s,-x,current[j+1])
        previous=current
    clause(-previous[bound])
def lex_le(left,right):
    prefix=fresh()
    clause(prefix)
    for a,b in zip(reversed(left),reversed(right)):
        clause(-prefix,-a,b)
        next_prefix=fresh()
        clause(-prefix,a,b,next_prefix)
        clause(-prefix,-a,-b,next_prefix)
        prefix=next_prefix

selectors=[[[fresh() for _ in range(n+i)] for _ in range(2)] for i in range(k)]
outputs=[fresh() for _ in range(k)]
for i in range(k):
    # All previous ANDs vanish on singleton inputs by induction.
    for v in range(n):clause(-selectors[i][0][v],-selectors[i][1][v])
    if args.side_order:lex_le(selectors[i][0],selectors[i][1])
if args.anchor_flag:
    assert args.mode=='plane' and args.positive_use and k>0
    # Every gate may be made true on some minimal true edge by pruning.
    # A verified incidence automorphism carries a first-gate edge to (0,0).
    a=conjunction(selectors[0][0][0],selectors[0][1][13])
    b=conjunction(selectors[0][1][0],selectors[0][0][13])
    clause(a,b)

if args.mode=='plane':
    data=json.loads(Path('/tmp/oec/pequalnp-pilot-60/structural-max-independent.json').read_text())
    tests=[(left|(right<<13),False) for left,right in data['rows']]
    edges=[(p,l) for p in range(13) for l in range(13) if (p-l)%13 in (0,1,3,9)]
    tests += [((1<<p)|(1<<(13+l)),True) for p,l in edges]
    graph=[]
    if args.row_cuts:
        # False-row choice signatures are injective. A row containing all of S
        # fixes the choice at every gate with a bare variable in S. Therefore
        # count(rows containing S) <= 2^(k - occurrence_union(S)).
        false_inputs=[left|(right<<13) for left,right in data['rows']]
        for width in (1,2):
            for subset in itertools.combinations(range(n),width):
                count=sum(all(x>>v&1 for v in subset) for x in false_inputs)
                if not count:continue
                bound=k-(count-1).bit_length()
                occurrence=[disjunction([selectors[i][side][v]
                                        for side in range(2) for v in subset]) for i in range(k)]
                at_most(occurrence,bound)
else:
    m=args.side
    graph=[fresh() for _ in range(m*m)]
    for i in range(m):clause(graph[i*m+i])
    for i in range(m):
        for j in range(i):clause(-graph[i*m+j],-graph[j*m+i])
    tests=[(x,None) for x in range(1<<n)]

positive_values=[[] for _ in range(k)]
for x,want in tests:
    values=[]
    for i in range(k):
        sides=[]
        for side in range(2):
            sels=selectors[i][side]
            terms=[sels[v] for v in range(n) if x>>v&1]
            terms += [conjunction(sels[n+j],values[j]) for j in range(i)]
            sides.append(disjunction(terms))
        values.append(conjunction(*sides))
    if want is True:
        for i,value in enumerate(values):positive_values[i].append(value)
    out=disjunction([conjunction(outputs[j],values[j]) for j in range(k)])
    if want is True:clause(out)
    elif want is False:clause(-out)
    else:
        terms=[graph[i*m+j] for i in range(m) for j in range(m)
               if x>>i&1 and x>>(m+j)&1]
        # Exact equality to the full quadratic graph function.
        for term in terms:clause(-term,out)
        clause(-out,*terms)
if args.positive_use:
    assert args.mode=='plane'
    for values in positive_values:clause(*values)

prefix=Path(args.prefix)
with prefix.with_suffix('.cnf').open('w') as f:
    f.write(f'p cnf {nv} {len(clauses)}\n')
    for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
metadata=dict(n=n,k=k,selectors=selectors,outputs=outputs,graph=graph,
              variables=nv,clauses=len(clauses),tests=len(tests),mode=args.mode,
              row_cuts=args.row_cuts,side_order=args.side_order,
              positive_use=args.positive_use,anchor_flag=args.anchor_flag)
prefix.with_suffix('.meta.json').write_text(json.dumps(metadata))
print(json.dumps({a:metadata[a] for a in ['n','k','variables','clauses','tests','mode']}))
