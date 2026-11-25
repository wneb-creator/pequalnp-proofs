from pathlib import Path
from itertools import product,combinations
from collections import Counter
import json
from fresh_mixedpair_exact import setup
from fresh_mixedrank import candidate
from fresh_case_charge import bits
import sys
r=json.loads(Path(sys.argv[1]).read_text());k=len(r['points']);g=r['groups'];b=len(g);E,stars,tabs=setup(k,g)
edges=[(i,k+j) for j,gg in enumerate(g) for i in gg]
fs=list(product(range(k),range(b)))
extra=[(0,0,'zero')]+[(stars[i],1<<i,'raw') for i in range(k+b)]+[(1<<e,(1<<p)|(1<<l),'flag') for e,(p,l) in enumerate(edges)]
hist=Counter();ex={}
for f1,f2 in combinations(fs,2):
 if candidate(g,[f1,f2])<4:continue
 for (i,j),(a,b) in ((f1,f2),(f2,f1)):
  r1=(1<<i)|(1<<(k+j));p1=stars[i]|stars[k+j]
  r2=(1<<a)|(1<<(k+b));p2=stars[a]|stars[k+b]
  for pe,re,kind in extra:
   basis={}
   for z,cs in tabs:
    live=list(cs)
    for P,rej in [(p1,not(z&r1)),(p2|pe,not(z&r2) and (not re or (z&re)!=re))]:
     if rej:
      v=0;remaining=[]
      for w in live:
       if w&P:v|=w
       else:remaining.append(w)
      live=remaining+([v] if v else [])
    for v in live:
     while v:
      h=v.bit_length()-1
      if h not in basis:basis[h]=v;break
      v^=basis[h]
    if len(basis)==E:break
   val=len(basis);hist[val]+=1
   if val not in ex:ex[val]=(i,j,a,b,re,kind)
print(sorted(hist.items()),ex[min(hist)])
