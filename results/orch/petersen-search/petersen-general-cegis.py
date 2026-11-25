import sys,json,time
from pathlib import Path
from datetime import datetime,timezone
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
m=int(sys.argv[1]);total_ms=int(sys.argv[2]);free=sys.argv[3] if len(sys.argv)>3 else 'not';n=12;idxwidth=(n+m).bit_length()
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x):return any(x>>a&1 and x>>b&1 for a,b in edges)
def extra(x):return not x&1 if free=='not' else free=='true' if free in ['true','false'] else bool(x&1)
patterns=[]
for first in [0,1]:
 for x in range(1024):
  if x&1!=first:continue
  if target(x):
   if all(not target(x^(1<<v)) for v in range(1,10) if x>>v&1):patterns.append(x)
  elif all(target(x|(1<<v)) for v in range(1,10) if not x>>v&1):patterns.append(x)
patterns=sorted(set(patterns))
s=z3.SolverFor('QF_BV');gates=[]
for i in range(m):
 op=z3.BitVec(f'op{i}',2);a=z3.BitVec(f'a{i}',idxwidth);b=z3.BitVec(f'b{i}',idxwidth)
 s.add(z3.ULE(op,2),z3.ULT(a,n+i),z3.ULT(b,n+i),z3.ULE(a,b),z3.Implies(op==2,b==a))
 gates.append((op,a,b))
if len(sys.argv)>4:
 fixed=json.loads(Path(sys.argv[4]).read_text())
 assert len(fixed['gates'])==m
 def virtual(w):return 11 if w==999 else w+1 if w>=11 else w
 for (op,a,b),(cop,ca,cb) in zip(gates,fixed['gates']):
  s.add(op=={'or':0,'and':1,'not':2}[cop],a==virtual(ca),b==virtual(cb))
for i in range(1,m):
 op,a,b=gates[i];op0,a0,b0=gates[i-1]
 s.add(z3.Or(a==n+i-1,b==n+i-1,z3.ULE(z3.Concat(op0,a0,b0),z3.Concat(op,a,b))))
for i in range(m-1):s.add(z3.Or([z3.Or(a==n+i,b==n+i) for op,a,b in gates[i+1:]]))
# Accepted repository row L6194 gives at least15 non-NOT gates for this function.
# Thus any candidate with at most18 gates has at most3 paid NOT gates.
s.add(z3.AtMost(*[op==2 for op,a,b in gates],max(0,m-15)))
def select(index,values):
 result=values[-1]
 for j in range(len(values)-2,-1,-1):result=z3.If(index==j,values[j],result)
 return result
added=set()
def add_pattern(x):
 if x in added:return
 vals=[z3.BoolVal(bool(x>>i&1)) for i in range(10)]+[z3.BoolVal(extra(x)),z3.BoolVal(False)]
 for i,(op,a,b) in enumerate(gates):
  va=select(a,vals);vb=select(b,vals);g=z3.Bool(f'v_{x}_{i}')
  s.add(g==z3.If(op==0,z3.Or(va,vb),z3.If(op==1,z3.And(va,vb),z3.Not(va))))
  vals.append(g)
 s.add(vals[-1]==target(x));added.add(x)
for x in patterns:add_pattern(x)
start=time.monotonic();iteration=0;history=[]
base=Path(f'/tmp/oec/pequalnp-pilot-152/gap-1884/petersen-general-size{m}-free{free}')
print(datetime.now(timezone.utc).isoformat(),'GENERAL CEGIS',m,'free',free,'paid_NOT_budget',max(0,m-15),'seedpatterns',len(added),flush=True)
while True:
 remaining=total_ms-int((time.monotonic()-start)*1000)
 if remaining<=0:print('RESULT unknown total_timeout',flush=True);break
 s.set(timeout=remaining);iteration+=1
 base.with_suffix('.smt2').write_text(s.to_smt2())
 st=time.monotonic();res=s.check();elapsed=time.monotonic()-st
 print('ITERATION',iteration,'patterns',len(added),'RESULT',res,'seconds',round(elapsed,3),flush=True)
 record=dict(iteration=iteration,patterns=sorted(added),result=str(res),seconds=elapsed)
 if res!=z3.sat:
  if res==z3.unknown:print('REASON',s.reason_unknown(),flush=True)
  history.append(record);break
 mo=s.model();desc=[[mo.eval(op).as_long(),mo.eval(a).as_long(),mo.eval(b).as_long()] for op,a,b in gates]
 full=[sum(1<<x for x in range(1024) if x>>i&1) for i in range(10)]+[sum(1<<x for x in range(1024) if extra(x)),0]
 fullmask=(1<<1024)-1
 for op,a,b in desc:full.append((full[a]|full[b]) if op==0 else (full[a]&full[b]) if op==1 else full[a]^fullmask)
 expected=sum(1<<x for x in range(1024) if target(x));errors=full[-1]^expected
 record['model']=desc;record['bad_inputs']=[x for x in range(1024) if errors>>x&1];history.append(record)
 if not errors:
  def actual(w):return 999 if w==11 else w-1 if w>=12 else w
  actualdesc=[[['or','and','not'][op],actual(a),actual(b)] for op,a,b in desc]
  data=dict(inputs=11,free_unary=free,gates=actualdesc,output=11+m-1,edges=edges)
  print('VERIFIED_FULL_TRUTH_TABLE',json.dumps(data),flush=True)
  base.with_name(base.name+'-model.json').write_text(json.dumps(data,indent=2));break
 print('COUNTEREXAMPLE_INPUTS',record['bad_inputs'],flush=True)
 for x in record['bad_inputs']:add_pattern(x)
base.with_name(base.name+'-history.json').write_text(json.dumps(history,indent=2))
print('TOTAL_SECONDS',round(time.monotonic()-start,3),flush=True)
print(s.statistics(),flush=True)
