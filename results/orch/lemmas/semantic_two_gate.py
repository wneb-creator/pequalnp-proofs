#!/usr/bin/env python3
import json
from collections import Counter
from pathlib import Path

E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
ALL=(1<<1024)-1
ROOT=[sum(1<<x for x in range(1024) if x>>i&1) for i in range(10)]
ROOT.append(ALL^ROOT[0])
F=0
for a,b in E:F|=ROOT[a]&ROOT[b]
def apply(op,a,b):return a|b if op else a&b
names=[f'x{i}' for i in range(10)]+['!x0']
records=[]
for v in (1,2):
 roots=[i for i in range(11) if i!=v]
 sensitive=sum(1<<x for x in range(1024) if not(x>>v&1) and not(F>>x&1) and F>>(x|(1<<v))&1)
 functions={ROOT[i]:names[i] for i in roots}
 first={}
 for a in roots:
  for b in roots:
   if a>b:continue
   for op in (0,1):
    h=apply(op,ROOT[a],ROOT[b]);s=f'({names[a]} {"OR" if op else "AND"} {names[b]})'
    first.setdefault(h,s);functions.setdefault(h,s)
 for h,s in first.items():
  for c in roots:
   for op in (0,1):
    g=apply(op,h,ROOT[c]);t=f'({s} {"OR" if op else "AND"} {names[c]})'
    functions.setdefault(g,t)
 for outer in (0,1):
  good={h:s for h,s in functions.items() if h&sensitive==(0 if outer else sensitive)}
  nonconstant={h:s for h,s in good.items() if h not in (0,ALL)}
  nonabsorbed={h:s for h,s in nonconstant.items() if h&(ALL^F)} if outer else nonconstant
  r={'vertex':v,'outer':'OR' if outer else 'AND','distinct_functions':len(functions),'passing':len(good),'nonconstant':len(nonconstant),'nonabsorbed_count':len(nonabsorbed),'nonabsorbed_examples':list(nonabsorbed.values())}
  records.append(r)
  print(json.dumps(r))
Path('results/orch/semantic-two-gate.json').write_text(json.dumps(records,indent=2)+'\n')
