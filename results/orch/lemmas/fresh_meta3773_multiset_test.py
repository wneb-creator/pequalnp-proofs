import sys,itertools,functools,ctypes,random,time
sys.argv=['','0'];import fresh_meta3773_extended_model as m
lib=ctypes.CDLL(str(m.job/'fresh-meta3773-readonce-multiset.so'));x=lib.feasible_multiset;x.argtypes=[ctypes.c_int,ctypes.POINTER(ctypes.c_uint64),ctypes.c_uint64,ctypes.c_uint64];x.restype=ctypes.c_int
def solve(F,p,n):return x(len(F),(ctypes.c_uint64*len(F))(*F),p,n)
r=random.Random(2343773);cnt=0
for size in range(2,15):
 for j in range(20):
  F=tuple(sorted(r.choices(m.raw+m.free,k=size)));p=m.target&r.getrandbits(m.NT);n=(m.target^m.M)&r.getrandbits(m.NT);assert solve(F,p,n)==m.feasible(F,p,n);cnt+=1
print('multiset/labelled recurrence comparisons',cnt)
F=tuple(sorted((*m.raw,*m.free,*m.raw[5:10])));p=m.target;n=(m.target^m.M);st=time.perf_counter();a=m.feasible(F,p,n);mid=time.perf_counter();b=solve(F,p,n);end=time.perf_counter();assert a==b;print('18-token direct comparison',a,'labelled seconds',mid-st,'grouped seconds',end-mid)
