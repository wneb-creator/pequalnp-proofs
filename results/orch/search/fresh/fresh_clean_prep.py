from itertools import permutations
from pathlib import Path
import json
from fresh_modules import modules
from fresh_affine_charge import affine,masks
from fresh_case_charge import bits,subsets

def write(r,autos=None):
 k=r['k'];groups=[tuple(g) for g in r['groups'] if len(g)>1];b=len(groups)
 gm=[sum(1<<i for i in a) for a in groups];rows=[sum(1<<j for j,g in enumerate(gm) if g>>i&1) for i in range(k)]
 if autos is None:
  autos=[]
  for p in permutations(range(k)):
   ng=[tuple(sorted(p[i] for i in g)) for g in groups]
   if set(ng)==set(groups):autos.append((p,[groups.index(g) for g in ng]))
 perms=[(masks(p),masks(l)) for p,l in autos]
 seen=set();reps=[]
 for ip in range(1<<k):
  nb=0
  for i in bits(ip):nb|=rows[i]
  for il in subsets(((1<<b)-1)^nb):
   if (ip,il) in seen:continue
   orb={(ps[ip],ls[il]) for ps,ls in perms};seen.update(orb);reps.append((ip,il,len(orb)))
 E=sum(map(len,groups));cap=E-b-1
 dest=Path('fresh-clean-'+r['id']+'.in')
 dest.write_text('\n'.join(' '.join(map(str,x)) for x in [(k,b,cap,len(reps)),gm,*reps])+'\n')
 print(r['id'],k,b,E,cap,len(reps),len(seen),len(autos),flush=True)

if __name__=='__main__':
 gm,rows,autos=affine()
 write(dict(id='affine3',k=9,groups=[tuple(bits(x)) for x in gm]),autos)
 for k in [6,7,8]:
  for r in modules(3,k):write(r)
