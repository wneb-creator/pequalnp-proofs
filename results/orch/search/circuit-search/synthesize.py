import argparse
import json
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('--gates',type=int,default=26)
parser.add_argument('--prefix',type=int)
parser.add_argument('--no-canon',action='store_true')
parser.add_argument('--allow-trivial',action='store_true')
parser.add_argument('--ordered-max',action='store_true')
parser.add_argument('--no-lex-order',action='store_true')
parser.add_argument('--no-liveness',action='store_true')
parser.add_argument('--minimal',action='store_true')
parser.add_argument('--dirty-and',action='store_true')
parser.add_argument('--edge-file')
parser.add_argument('--output',required=True)
args=parser.parse_args()

edges=[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
ninputs=14
if args.edge_file:
 data=json.loads(Path(args.edge_file).read_text())
 edges=[tuple(e) for e in data['edges']];ninputs=data['ninputs']
 if not args.no_canon:raise SystemExit('Custom graph requires --no-canon')
positive_count=len(edges)
def target(m): return any((m>>a)&(m>>b)&1 for a,b in edges)
rows=[(1<<a)|(1<<b) for a,b in edges]
rows.extend(m for m in range(1<<ninputs) if not target(m) and all(target(m|(1<<i)) for i in range(ninputs) if not ((m>>i)&1)))
canon=[226,227,228,232,233,234,236,239,258,259,260,262,263,264,266,267,269,277,278,281,284,338,341,344,354,355,356,359,402,404,1576,1577,1582,1583,1584,1589,1592,1593,1598,1599,1601,1604,1609,1611,1614,1617,1619,2026,2027,2032,2034,2036,2039,2042,2043,2045,2047,2048,2051,2053,2054,2058,2066,2067,2069]
nv=0
clauses=[]
def var():
 global nv
 nv+=1
 return nv
def clause(*lits):
 lits=set(lits)
 if 0 in lits: raise ValueError('zero literal')
 if any(-x in lits for x in lits): return
 clauses.append(tuple(sorted(lits,key=abs)))
def exactly_one(xs):
 clause(*xs)
 # Sequential encoding for at-most-one.
 if len(xs)<2:return
 acc=xs[0]
 for x in xs[1:-1]:
  y=var()
  clause(-acc,y);clause(-x,y);clause(-acc,-x)
  acc=y
 clause(-acc,-xs[-1])

truth=var();clause(truth)
values=[[truth if (r>>i)&1 else -truth for r in rows] for i in range(ninputs)]
structure=[]
for i in range(args.gates):
 n=ninputs+i
 left=[var() for _ in range(n)]
 right=[var() for _ in range(n)]
 op=var() # true means OR
 exactly_one(left);exactly_one(right)
 for a in range(n):
  for b in range(a):clause(-left[a],-right[b])
 if i<2:
  for a in range(n):clause(-left[a],-right[a])
 lv=[var() for _ in rows];rv=[var() for _ in rows];out=[var() for _ in rows]
 for side,sv in [(left,lv),(right,rv)]:
  for wire,s in enumerate(side):
   for r in range(len(rows)):
    clause(-s,-sv[r],values[wire][r]);clause(-s,sv[r],-values[wire][r])
 for a,b,y in zip(lv,rv,out):
  # Conditional AND and OR equivalences.
  clause(op,-y,a);clause(op,-y,b);clause(op,y,-a,-b)
  clause(-op,y,-a);clause(-op,y,-b);clause(-op,-y,a,b)
 if not args.allow_trivial:
  clause(*out[:positive_count])
  clause(*[-x for x in out[positive_count:]])
 if args.minimal:
  for old in values:
   witnesses=[]
   for r,(a,b) in enumerate(zip(out,old)):
    # Old wire fails to dominate this gate on boundary rows.
    d=var();witnesses.append(d)
    if r<positive_count:
     clause(-d,a);clause(-d,-b)
    else:
     clause(-d,-a);clause(-d,b)
   clause(*witnesses)
 if args.ordered_max and i:
  prev=structure[-1]
  for a in range(n-1):
   for b in range(a):clause(-prev['right'][a],-right[b])
 if not args.no_lex_order and i:
  prev=structure[-1]
  dep=right[-1]
  eql=var();eqr=var()
  for a in range(n-1):
   clause(-prev['left'][a],-left[a],eql)
   clause(-prev['right'][a],-right[a],eqr)
   for b in range(a):
    clause(dep,-prev['left'][a],-left[b])
    clause(dep,-eql,-prev['right'][a],-right[b])
  clause(dep,-eql,-eqr,-prev['op'],op)
 values.append(out)
 structure.append({'left':left,'right':right,'op':op,'out':out})

if not args.no_liveness:
 for wire in range(ninputs-1+args.gates):
  uses=[]
  for i,s in enumerate(structure):
   if wire<ninputs+i:uses.extend([s['left'][wire],s['right'][wire]])
  clause(*uses)

if args.dirty_and:
 dirty=[]
 for s in structure:
  for y in s['out'][positive_count:]:
   d=var();dirty.append(d)
   clause(-d,-s['op']);clause(-d,y)
 clause(*dirty)

if not args.no_canon:
 first,second=structure[:2]
 clause(first['left'][0])
 candidates=canon if args.prefix is None else [canon[args.prefix]]
 selectors=[var() for _ in candidates]
 exactly_one(selectors)
 for s,t in zip(selectors,candidates):
  b=t//225;c=t%225//15;d=t%15
  clause(-s,first['right'][b])
  clause(-s,second['left'][c]);clause(-s,second['right'][d])
for r,v in zip(rows,values[-1]):clause(v if target(r) else -v)
path=Path(args.output)
with path.open('w') as f:
 f.write(f'p cnf {nv} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
path.with_suffix('.map.json').write_text(json.dumps({'gates':args.gates,'structure':structure,'rows':rows,'nv':nv,'clauses':len(clauses),'prefix':args.prefix,'ninputs':ninputs,'edges':edges}))
print(json.dumps({'file':str(path),'gates':args.gates,'variables':nv,'clauses':len(clauses),'rows':len(rows),'prefix':args.prefix}),flush=True)
