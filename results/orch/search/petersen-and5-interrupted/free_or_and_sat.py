import runpy,time,json,itertools
from pathlib import Path
core=runpy.run_path('/tmp/oec/pequalnp-pilot-87/proof_structure/tiny_graph_counts.py')
CNF,lib,CB=core['CNF'],core['lib'],core['CB']
def solve(n,edges,k,limit):
 c=CNF();sels=[([c.var() for _ in range(n+i)],[c.var() for _ in range(n+i)]) for i in range(k)];final=[c.var() for _ in range(k)]
 for row in range(1<<n):
  gs=[]
  for i,(left,right) in enumerate(sels):
   args=[]
   for ss in [left,right]:
    ts=[ss[j] for j in range(n) if row>>j&1]
    for j,v in enumerate(gs):
     s=ss[n+j];t=c.var();c.add(-t,s);c.add(-t,v);c.add(t,-s,-v);ts.append(t)
    a=c.var();c.add(-a,*ts)
    for t in ts:c.add(-t,a)
    args.append(a)
   a,b=args;z=c.var();c.add(-z,a);c.add(-z,b);c.add(z,-a,-b);gs.append(z)
  out=[]
  for s,v in zip(final,gs):
   t=c.var();c.add(-t,s);c.add(-t,v);c.add(t,-s,-v);out.append(t)
  yes=any((row>>a)&(row>>b)&1 for a,b in edges)
  if yes:c.add(*out)
  else:
   for t in out:c.add(-t)
 solver=lib.sat_init();lib.sat_set_option(solver,b'quiet',1)
 for clause in c.cs:
  for v in clause:lib.sat_add(solver,v)
  lib.sat_add(solver,0)
 started=time.monotonic();deadline=started+limit
 @CB
 def terminate(_):return int(time.monotonic()>deadline)
 lib.sat_set_terminate(solver,None,terminate);result=lib.sat_solve(solver);model=[];outs=[]
 if result==10:
  for a,b in sels:model.append(([j for j,v in enumerate(a) if lib.sat_val(solver,v)>0],[j for j,v in enumerate(b) if lib.sat_val(solver,v)>0]))
  outs=[j for j,v in enumerate(final) if lib.sat_val(solver,v)>0]
  for row in range(1<<n):
   vals=[bool(row>>j&1) for j in range(n)]
   for a,b in model:vals.append(any(vals[j] for j in a) and any(vals[j] for j in b))
   assert any(vals[n+j] for j in outs)==any((row>>a)&(row>>b)&1 for a,b in edges)
 record={'n':n,'edges':edges,'and_cap':k,'or_cap':None,'variables':c.n,'clauses':len(c.cs),'seconds':round(time.monotonic()-started,3),'status':{0:'UNKNOWN',10:'SAT',20:'UNSAT'}[result],'and_operands':model,'output_or':outs}
 lib.sat_release(solver);print(json.dumps(record),flush=True)
if __name__=='__main__':
 solve(5,[(i,(i+1)%5) for i in range(5)],3,5)
 solve(5,[(i,(i+1)%5) for i in range(5)],2,5)
 solve(7,[(i,(i+1)%7) for i in range(7)],3,12)
 solve(10,[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)],5,25)
