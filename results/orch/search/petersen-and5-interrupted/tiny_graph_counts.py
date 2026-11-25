import ctypes,itertools,time,json
from pathlib import Path
lib=ctypes.CDLL('/tmp/oec/pequalnp-pilot-87/counterexample/libcadical.so')
lib.sat_init.argtypes=[];lib.sat_init.restype=ctypes.c_void_p
for f in ['add','assume']:getattr(lib,'sat_'+f).argtypes=[ctypes.c_void_p,ctypes.c_int]
lib.sat_solve.argtypes=[ctypes.c_void_p];lib.sat_solve.restype=ctypes.c_int
lib.sat_val.argtypes=[ctypes.c_void_p,ctypes.c_int];lib.sat_val.restype=ctypes.c_int
lib.sat_set_option.argtypes=[ctypes.c_void_p,ctypes.c_char_p,ctypes.c_int]
lib.sat_release.argtypes=[ctypes.c_void_p]
CB=ctypes.CFUNCTYPE(ctypes.c_int,ctypes.c_void_p)
lib.sat_set_terminate.argtypes=[ctypes.c_void_p,ctypes.c_void_p,CB]
class CNF:
 def __init__(self):self.n=0;self.cs=[]
 def var(self):self.n+=1;return self.n
 def add(self,*ls):self.cs.append(ls)
 def one(self,vs):
  self.add(*vs)
  for a,b in itertools.combinations(vs,2):self.add(-a,-b)
def solve(n,edges,gates,count_kind,count_cap,seconds):
 start=time.monotonic();c=CNF();ops=[];ls=[];rs=[]
 for i in range(gates):
  op=c.var();a=[c.var() for _ in range(n+i)];b=[c.var() for _ in range(n+i)];c.one(a);c.one(b)
  for j in range(n+i):
   for k in range(j):c.add(-a[j],-b[k])
  ops.append(op);ls.append(a);rs.append(b)
 if count_kind is not None:
  literals=ops if count_kind=='and' else [-o for o in ops]
  for xs in itertools.combinations(literals,count_cap+1):c.add(*[-x for x in xs])
 for row in range(1<<n):
  values=[]
  for j in range(n):v=c.var();c.add(v if row>>j&1 else -v);values.append(v)
  for i in range(gates):
   a,b,z=c.var(),c.var(),c.var()
   for selector,arg in [(ls[i],a),(rs[i],b)]:
    for s,v in zip(selector,values):c.add(-s,-arg,v);c.add(-s,arg,-v)
   op=ops[i]
   c.add(-op,-z,a);c.add(-op,-z,b);c.add(-op,z,-a,-b)
   c.add(op,z,-a);c.add(op,z,-b);c.add(op,-z,a,b)
   values.append(z)
  target=any((row>>a)&(row>>b)&1 for a,b in edges);c.add(values[-1] if target else -values[-1])
 solver=lib.sat_init();lib.sat_set_option(solver,b'quiet',1)
 for clause in c.cs:
  for v in clause:lib.sat_add(solver,v)
  lib.sat_add(solver,0)
 deadline=time.monotonic()+seconds
 @CB
 def terminate(_):return int(time.monotonic()>deadline)
 lib.sat_set_terminate(solver,None,terminate);result=lib.sat_solve(solver);model=[]
 if result==10:
  for i in range(gates):
   op=lib.sat_val(solver,ops[i])>0;a=next(j for j,v in enumerate(ls[i]) if lib.sat_val(solver,v)>0);b=next(j for j,v in enumerate(rs[i]) if lib.sat_val(solver,v)>0);model.append((int(op),a,b))
  for row in range(1<<n):
   vs=[bool(row>>j&1) for j in range(n)]
   for op,a,b in model:vs.append(vs[a] and vs[b] if op else vs[a] or vs[b])
   assert vs[-1]==any((row>>a)&(row>>b)&1 for a,b in edges)
  if count_kind is not None:assert sum(op==(count_kind=='and') for op,_,_ in model)<=count_cap
 lib.sat_release(solver)
 rec={'n':n,'edges':edges,'gate_cap':gates,'count_kind':count_kind,'count_cap':count_cap,'status':{0:'UNKNOWN',10:'SAT',20:'UNSAT'}[result],'seconds':round(time.monotonic()-start,3),'variables':c.n,'clauses':len(c.cs),'model':model}
 print(json.dumps(rec),flush=True);return rec
if __name__=='__main__':
 solve(4,[(0,1),(1,2),(2,3)],4,None,None,5)
 for n in [5,6,7]:
  edges=[(i,(i+1)%n) for i in range(n)];tau=(n+1)//2;cap=n+tau+3
  solve(n,edges,cap,'and',tau-1,12)
  solve(n,edges,cap,'or',n-2,12)
