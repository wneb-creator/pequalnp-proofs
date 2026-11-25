import z3,math,itertools,json,time,sys
from pathlib import Path

def synth(n,edges,s,sound=False,unsound=False,timeout=180000,symmetry=True):
 t0=time.monotonic(); width=1<<n; iw=max(1,(n+s).bit_length()); allmask=(1<<width)-1
 inputs=[sum(1<<a for a in range(width) if a>>i&1) for i in range(n)]
 target=sum(1<<a for a in range(width) if any(a>>u&1 and a>>v&1 for u,v in edges))
 vals=[z3.BitVecVal(v,width) for v in inputs]
 sol=z3.SolverFor('QF_BV');sol.set(timeout=timeout)
 aa=[];bb=[];oo=[];unsafe=[]
 for j in range(s):
  a=z3.BitVec('a'+str(j),iw);b=z3.BitVec('b'+str(j),iw);op=z3.Bool('and'+str(j));v=z3.BitVec('v'+str(j),width)
  sol.add(z3.ULT(a,b),z3.ULT(b,n+j))
  def pick(k):
   r=vals[-1]
   for i in range(len(vals)-2,-1,-1):r=z3.If(k==i,vals[i],r)
   return r
  x=pick(a);y=pick(b)
  sol.add(v==z3.If(op,x&y,x|y))
  for w in vals:sol.add(v!=w)
  bad=z3.And(op,v&z3.BitVecVal(allmask^target,width)!=0)
  if sound:sol.add(z3.Not(bad))
  unsafe.append(bad)
  aa.append(a);bb.append(b);oo.append(op);vals.append(v)
  if j and symmetry:
   prevord=z3.Concat(aa[j-1],bb[j-1],z3.If(oo[j-1],z3.BitVecVal(0,1),z3.BitVecVal(1,1)))
   currord=z3.Concat(a,b,z3.If(op,z3.BitVecVal(0,1),z3.BitVecVal(1,1)))
   sol.add(z3.Or(a==n+j-1,b==n+j-1,z3.ULE(prevord,currord)))
 for j in range(s-1):sol.add(z3.Or(*[z3.Or(aa[k]==n+j,bb[k]==n+j) for k in range(j+1,s)]))
 if unsound:sol.add(z3.Or(*unsafe))
 sol.add(vals[-1]==target)
 r=sol.check();result={'n':n,'edges':edges,'size':s,'sound':sound,'unsound':unsound,'result':str(r),'seconds':time.monotonic()-t0}
 if r==z3.sat:
  model=sol.model();result['gates']=[('and' if z3.is_true(model.eval(o)) else 'or',model.eval(a).as_long(),model.eval(b).as_long()) for a,b,o in zip(aa,bb,oo)]
  vv=inputs[:];bad=[]
  for j,(op,a,b) in enumerate(result['gates']):
   v=vv[a]&vv[b] if op=='and' else vv[a]|vv[b]
   if op=='and' and (v&~target):bad.append(j)
   vv.append(v)
  assert vv[-1]==target
  result['unsafe_ands']=bad
 if r==z3.unknown:result['reason']=sol.reason_unknown()
 return result

CASES={'P5':(5,[(0,1),(1,2),(2,3),(3,4)],5),'C5':(5,[(0,1),(1,2),(2,3),(3,4),(4,0)],7),'fork5':(5,[(0,1),(0,2),(0,3),(3,4)],5),'P6':(6,[(0,1),(1,2),(2,3),(3,4),(4,5)],7),'C6':(6,[(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)],8)}
if __name__=='__main__':
 for name,(n,e,s) in CASES.items():
  for k,sound,unsound in [(s-1,False,False),(s,True,False),(s,False,True)]:
   r=synth(n,e,k,sound,unsound);r['name']=name
   with Path('/tmp/oec/pequalnp-pilot-55/counterexample-sat-results.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
   print(json.dumps(r),flush=True)
