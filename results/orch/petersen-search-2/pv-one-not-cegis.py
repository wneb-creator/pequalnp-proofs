import sys,json,time
from pathlib import Path
from itertools import combinations
from datetime import datetime,timezone
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
m=int(sys.argv[1]);limit=int(sys.argv[2]);notcount=int(sys.argv[3]) if len(sys.argv)>3 else 1;mode=sys.argv[4] if len(sys.argv)>4 else 'general'
p=9;n=10;idxwidth=(n+m).bit_length()
original=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
edges=[(a-1,b-1) for a,b in original if a and b]
def target(x):return any(x>>a&1 and x>>b&1 for a,b in edges)
patterns=sorted(set([x for x in range(512) if not target(x)]+[(1<<a)|(1<<b) for a,b in edges]+[511]+[511^(1<<i) for i in range(9)]))
s=z3.SolverFor('QF_BV');gates=[]
for i in range(m):
 op=z3.BitVec(f'op{i}',2);a=z3.BitVec(f'a{i}',idxwidth);b=z3.BitVec(f'b{i}',idxwidth)
 s.add(z3.ULE(op,2),z3.ULT(a,n+i),z3.ULT(b,n+i),z3.ULE(a,b),z3.Implies(op==2,b==a));gates.append((op,a,b))
s.add(z3.PbEq([(op==2,1) for op,a,b in gates],notcount))
# If the only NOT is the output, the result is antitone in every input.
if notcount==1:s.add(gates[-1][0]!=2)
for i in range(1,m):
 op,a,b=gates[i];op0,a0,b0=gates[i-1]
 s.add(z3.Or(a==n+i-1,b==n+i-1,z3.ULE(z3.Concat(op0,a0,b0),z3.Concat(op,a,b))))
for i in range(m-1):s.add(z3.Or([z3.Or(a==n+i,b==n+i) for op,a,b in gates[i+1:]]))
if mode=='control':
 desc=[]
 def add(op,a,b):desc.append([op,a,b]);return n+len(desc)-1
 cover=next(S for S in combinations(range(p),5) if all(a in S or b in S for a,b in edges));pending=set(edges);terms=[]
 for v in cover:
  es=[e for e in sorted(pending) if v in e]
  if not es:continue
  ns=[b if a==v else a for a,b in es];pending.difference_update(es);z=ns[0]
  for w in ns[1:]:z=add(0,z,w)
  terms.append(add(1,v,z))
 out=terms[0]
 for w in terms[1:]:out=add(0,out,w)
 assert len(desc)==16
 if notcount==1:
  true=add(2,9,9);out=add(1,out,true)
 mapping={i:i for i in range(n)};ordered=[];todo=set(range(len(desc)))
 while todo:
  ready=[]
  for i in todo:
   op,a,b=desc[i]
   if a in mapping and b in mapping:
    aa,bb=sorted([mapping[a],mapping[b]]);ready.append(((op,aa,bb),i,op,aa,bb))
  _,i,op,a,b=min(ready);mapping[n+i]=n+len(ordered);ordered.append([op,a,b]);todo.remove(i)
 assert len(ordered)==m and mapping[out]==n+m-1
 for (op,a,b),(cop,ca,cb) in zip(gates,ordered):s.add(op==cop,a==ca,b==cb)
def select(index,vals):
 result=vals[-1]
 for j in range(len(vals)-2,-1,-1):result=z3.If(index==j,vals[j],result)
 return result
added=set()
def add_pattern(x):
 if x in added:return
 vals=[z3.BoolVal(bool(x>>i&1)) for i in range(p)]+[z3.BoolVal(False)]
 for i,(op,a,b) in enumerate(gates):
  va=select(a,vals);vb=select(b,vals);g=z3.Bool(f'v_{x}_{i}')
  s.add(g==z3.If(op==0,z3.Or(va,vb),z3.If(op==1,z3.And(va,vb),z3.Not(va))));vals.append(g)
 s.add(vals[-1]==target(x));added.add(x)
for x in patterns:add_pattern(x)
base=Path(f'/tmp/oec/pequalnp-pilot-152/gap-1884/pv-size{m}-exactnot{notcount}-{mode}')
start=time.monotonic();iteration=0;history=[]
print(datetime.now(timezone.utc).isoformat(),'PV9',m,'gates','exactNOT',notcount,'mode',mode,'seed',len(added),flush=True)
while True:
 remaining=limit-int((time.monotonic()-start)*1000)
 if remaining<=0:print('RESULT unknown total_timeout',flush=True);break
 s.set(timeout=remaining);iteration+=1;base.with_suffix('.smt2').write_text(s.to_smt2());t=time.monotonic();res=s.check();elapsed=time.monotonic()-t
 print('ITERATION',iteration,'patterns',len(added),'RESULT',res,'seconds',round(elapsed,3),flush=True)
 record=dict(iteration=iteration,patterns=sorted(added),result=str(res),seconds=elapsed)
 if res!=z3.sat:
  if res==z3.unknown:print('REASON',s.reason_unknown(),flush=True)
  history.append(record);break
 mo=s.model();desc=[[mo.eval(op).as_long(),mo.eval(a).as_long(),mo.eval(b).as_long()] for op,a,b in gates]
 full=[sum(1<<x for x in range(512) if x>>i&1) for i in range(p)]+[0]
 for op,a,b in desc:full.append(full[a]|full[b] if op==0 else full[a]&full[b] if op==1 else full[a]^((1<<512)-1))
 errors=full[-1]^sum(1<<x for x in range(512) if target(x));bad=[x for x in range(512) if errors>>x&1]
 record['model']=desc;record['bad_inputs']=bad;history.append(record)
 if not bad:
  def actual(w):return 999 if w==9 else w-1 if w>=10 else w
  data=dict(inputs=p,gates=[[['or','and','not'][op],actual(a),actual(b)] for op,a,b in desc],output=p+m-1,edges=edges,not_count=notcount)
  print('VERIFIED_FULL512',json.dumps(data),flush=True);base.with_name(base.name+'-model.json').write_text(json.dumps(data,indent=2));break
 print('COUNTEREXAMPLE_INPUTS',bad,flush=True)
 for x in bad:add_pattern(x)
base.with_name(base.name+'-history.json').write_text(json.dumps(history,indent=2));print('TOTAL_SECONDS',round(time.monotonic()-start,3),flush=True);print(s.statistics(),flush=True)
