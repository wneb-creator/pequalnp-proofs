from collections import deque
from itertools import product
from pathlib import Path
from fresh_case_charge import bits,subsets
from fresh_affine_charge import masks
from fresh_modules import norm
q=3
pts=sorted({norm(p,q) for p in product(range(q),repeat=3) if any(p)})
gs=[sum(1<<i for i,p in enumerate(pts) if sum(a*b for a,b in zip(l,p))%q==0) for l in pts]
def act(fn):return tuple(pts.index(norm(fn(p),q)) for p in pts)
pgens=[act(lambda p:(p[1],p[0],p[2])),act(lambda p:(p[0],p[2],p[1])),act(lambda p:((p[0]+p[1])%q,p[1],p[2])),act(lambda p:((-p[0])%q,p[1],p[2]))]
perms=[]
for p in pgens:
 ps=masks(p);l=[gs.index(ps[v]) for v in gs];perms.append((ps,masks(l)))
seen=set();rep=[]
for ip in range(1<<13):
 nb=0
 for i in bits(ip):nb|=gs[i]
 for il in subsets(8191^nb):
  if (ip,il) in seen:continue
  todo=deque([(ip,il)]);seen.add((ip,il));size=0
  while todo:
   p,l=todo.popleft();size+=1
   for pp,lp in perms:
    t=(pp[p],lp[l])
    if t not in seen:seen.add(t);todo.append(t)
  rep.append((ip,il,size))
for cap in range(21,27):
 Path('fresh-clean-plane3-'+str(cap)+'.in').write_text('\n'.join(' '.join(map(str,x)) for x in [(13,13,cap,len(rep)),gs,*rep])+'\n')
print(len(rep),len(seen))
