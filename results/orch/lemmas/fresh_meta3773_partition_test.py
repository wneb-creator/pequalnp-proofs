import sys,itertools,random,time,ctypes
sys.argv=['p','1'];import fresh_meta3773_five_partition as pr
import fresh_meta3773_five_wide as prior
m=pr.model;R=random.Random(23773);counts=[0,0];F0=m.raw+m.free;st=time.perf_counter()
for n in range(2,15):
 for j in range(24):
  F=tuple(sorted(R.choices(F0,k=n)));v=list(F)
  while len(v)>1:
   a=v.pop(R.randrange(len(v))); b=v.pop(R.randrange(len(v)));v.append((a&b)if R.randrange(2)else(a|b))
  if j%2:p=v[0];q=m.M^p
  else:p=m.target;q=m.M^p
  was=prior.solve(F,p,q);x=(ctypes.c_uint64*len(F))(*F);ok=pr.partition(len(F),x,p,q);assert not was or ok;assert pr.solve(F,p,q)==was;counts[bool(ok)]+=1
print('positive/negative prior readonce crosschecks pass',sum(counts),'root-rejected',counts[0],'seconds',time.perf_counter()-st)
for mask in [127,63,126,31]:
 F=tuple(sorted((*m.raw,*(v for j,v in enumerate(m.free)if mask>>j&1))));x=(ctypes.c_uint64*len(F))(*F);st=time.perf_counter();a=pr.partition(len(F),x,m.target,m.M^m.target);print(mask,'root permitted',a,'seconds',time.perf_counter()-st)
