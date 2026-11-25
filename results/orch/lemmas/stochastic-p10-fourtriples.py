from pathlib import Path
from itertools import combinations,product
from collections import Counter
import json,time
start=time.monotonic()
T=[11,69,98,49]
M=[m for m in range(128)]
options=[]
for t in T:
 pairs=[(p,) for p in M if p.bit_count()==2 and p&t==p]
 fours=[(p,) for p in M if p.bit_count()==4 and p&t==t]
 fives=[(a,b) for a,b in combinations([p for p in M if p.bit_count()==5],2) if a&b==t]
 assert len(pairs)==3 and len(fours)==4 and len(fives)==3
 options.append(pairs+fours+fives)
small={0}|{1<<i for i in range(7)}
outside={m for m in M if m.bit_count()==2 and all(m&t!=m for t in T)}
families={}
hist=Counter()
for choices in product(range(10),repeat=4):
 family=frozenset(T)|frozenset(x for i,k in enumerate(choices) for x in options[i][k])
 hist[len(family)]+=1
 if len(family)<=8:families.setdefault(tuple(sorted(family)),choices)
def closure(family):
 allowed=small|outside|set(family)
 known={m for m in allowed if m.bit_count()<=2}
 while True:
  new=known.copy()
  for a,b in combinations(known,2):
   if a|b in allowed:new.add(a|b)
   if a&b in allowed:new.add(a&b)
  if new==known:return known
  known=new
rows=[];shapes=Counter();unreachable=[]
for family,choices in sorted(families.items()):
 known=closure(family)
 row=dict(family=list(family),choices=list(choices),known=sorted(known),missing=sorted(set(family)-known))
 if not row['missing']:
  rows.append(row);shapes[tuple(sorted(Counter(m.bit_count() for m in family).items()))]+=1
 else:unreachable.append(row)
result=dict(scope='Finite parent-family and union/intersection closure census for p10 I0123, missing456. Y<=8 is a separate actual-circuit count premise. All empty/singleton and outside-triple pairs are granted; no formula equivalence assumed.',triples=T,parent_options=options,outside_pairs=sorted(outside),choice_histogram=dict(hist),families_at_most8=len(families),constructible_count=len(rows),constructible_shapes={str(k):v for k,v in shapes.items()},constructible=rows,unreachable=unreachable,seconds=time.monotonic()-start)
Path('results/orch/lemmas/stochastic-p10-fourtriples.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['constructible','unreachable','parent_options']}))
