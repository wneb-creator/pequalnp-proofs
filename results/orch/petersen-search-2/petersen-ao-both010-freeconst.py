import sys,json,time
from pathlib import Path
from itertools import combinations
from datetime import datetime,timezone
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
m=int(sys.argv[1]);limit=int(sys.argv[2]);mode=sys.argv[3] if len(sys.argv)>3 else 'general'
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x):return any(x>>a&1 and x>>b&1 for a,b in edges)
patterns=[]
for first in [0,1]:
 for x in range(1024):
  if x&1!=first:continue
  if target(x):
   if all(not target(x^(1<<v)) for v in range(1,10) if x>>v&1):patterns.append(x)
  elif all(target(x|(1<<v)) for v in range(1,10) if not x>>v&1):patterns.append(x)
patterns=sorted(set(patterns));width=len(patterns);n=13;idxwidth=(n+m).bit_length()
inputs=[sum(1<<j for j,x in enumerate(patterns) if x>>i&1) for i in range(10)]
inputs += [sum(1<<j for j,x in enumerate(patterns) if not x&1),0,(1<<width)-1]
expected=sum(1<<j for j,x in enumerate(patterns) if target(x))
s=z3.SolverFor('QF_BV');s.set(timeout=limit)
signals=[z3.BitVecVal(x,width) for x in inputs];gates=[]
def select(index,values):
 result=values[-1]
 for j in range(len(values)-2,-1,-1):result=z3.If(index==j,values[j],result)
 return result
for i in range(m):
 a=z3.BitVec(f'a{i}',idxwidth);b=z3.BitVec(f'b{i}',idxwidth);op=z3.Bool(f'or{i}')
 s.add(z3.ULT(a,n+i),z3.ULT(b,n+i),z3.ULE(a,b))
 g=z3.BitVec(f'g{i}',width);s.add(g==z3.If(op,select(a,signals)|select(b,signals),select(a,signals)&select(b,signals)))
 signals.append(g);gates.append((op,a,b,g))
for i in range(1,m):
 op,a,b,g=gates[i];op0,a0,b0,g0=gates[i-1]
 key=z3.Concat(z3.If(op,z3.BitVecVal(0,1),z3.BitVecVal(1,1)),a,b)
 key0=z3.Concat(z3.If(op0,z3.BitVecVal(0,1),z3.BitVecVal(1,1)),a0,b0)
 s.add(z3.Or(a==n+i-1,b==n+i-1,z3.ULE(key0,key)))
for i in range(m-1):s.add(z3.Or([z3.Or(a==n+i,b==n+i) for op,a,b,g in gates[i+1:]]))
s.add(signals[-1]==z3.BitVecVal(expected,width))
if mode=='both010':
 raw=[z3.Or(a==0,b==0) for op,a,b,g in gates]
 neg=[z3.Or(a==10,b==10) for op,a,b,g in gates]
 s.add(z3.PbEq([(r,1) for r in raw],1),z3.PbEq([(r,1) for r in neg],1))
 for i,(op,a,b,g) in enumerate(gates):s.add(z3.Implies(raw[i],op),z3.Implies(neg[i],z3.Not(op)))
 for v in range(1,10):s.add(z3.AtMost(*[z3.Or(a==v,b==v) for op,a,b,g in gates],3))
if mode=='canonical':
 cover=next(S for S in combinations(range(10),6) if all(a in S or b in S for a,b in edges))
 pending=set(edges);desc=[];terms=[]
 def add(op,a,b):desc.append([op,a,b]);return n+len(desc)-1
 for v in cover:
  es=[e for e in sorted(pending) if v in e]
  if not es:continue
  ns=[b if a==v else a for a,b in es];pending.difference_update(es)
  z=ns[0]
  for w in ns[1:]:z=add(True,z,w)
  terms.append(add(False,v,z))
 out=terms[0]
 for t in terms[1:]:out=add(True,out,t)
 # Greedy least-key topological reordering, preserving the designated final output.
 mapping={i:i for i in range(n)};ordered=[];todo=set(range(len(desc)))
 while todo:
  ready=[]
  for i in todo:
   op,a,b=desc[i]
   if a in mapping and b in mapping:
    aa,bb=sorted([mapping[a],mapping[b]]);ready.append(((0 if op else 1,aa,bb),i,op,aa,bb))
  _,i,op,a,b=min(ready);mapping[n+i]=n+len(ordered);ordered.append([op,a,b]);todo.remove(i)
 assert len(ordered)==m and mapping[out]==n+m-1
 for (op,a,b,g),(cop,ca,cb) in zip(gates,ordered):s.add(op==cop,a==ca,b==cb)
Path(f'/tmp/oec/pequalnp-pilot-152/gap-1884/petersen-ao-freeconst-size{m}-{mode}.smt2').write_text(s.to_smt2())
print(datetime.now(timezone.utc).isoformat(),'PETERSEN',m,'AO gates, freeNOTx0 andbothconstants','patterns',width,'mode',mode,flush=True)
start=time.monotonic();res=s.check();print('RESULT',res,'seconds',round(time.monotonic()-start,3),flush=True)
if res==z3.sat:
 mo=s.model();desc=[[bool(z3.is_true(mo.eval(op))),mo.eval(a).as_long(),mo.eval(b).as_long()] for op,a,b,g in gates]
 full=[sum(1<<x for x in range(1024) if x>>i&1) for i in range(10)]+[sum(1<<x for x in range(1024) if not x&1),0,(1<<1024)-1]
 for op,a,b in desc:full.append((full[a]|full[b]) if op else (full[a]&full[b]))
 assert full[-1]==sum(1<<x for x in range(1024) if target(x))
 mapping=[('wire',i) for i in range(11)]+[('const',False),('const',True)];actualdesc=[]
 for op,a,b in desc:
  aa,bb=mapping[a],mapping[b]
  if aa[0]=='const' and bb[0]=='const':r=('const',(aa[1] or bb[1]) if op else (aa[1] and bb[1]))
  elif aa[0]=='const':r=aa if aa[1]==op else bb
  elif bb[0]=='const':r=bb if bb[1]==op else aa
  elif aa==bb:r=aa
  else:
   actualdesc.append(['or' if op else 'and',aa[1],bb[1]]);r=('wire',10+len(actualdesc))
  mapping.append(r)
 assert mapping[-1][0]=='wire'
 data=dict(inputs=11,free_unary='not_x0',gates=actualdesc,output=mapping[-1][1],edges=edges)
 # Constant propagation preserves all assignments; verify the extracted actual circuit again.
 verify=[sum(1<<x for x in range(1024) if x>>i&1) for i in range(10)]+[sum(1<<x for x in range(1024) if not x&1)]
 for op,a,b in actualdesc:verify.append(verify[a]|verify[b] if op=='or' else verify[a]&verify[b])
 assert verify[data['output']]==sum(1<<x for x in range(1024) if target(x))
 print('VERIFIED_FULL_TRUTH_TABLE',json.dumps(data),flush=True)
 Path(f'/tmp/oec/pequalnp-pilot-152/gap-1884/petersen-ao-freeconst-size{m}-{mode}-model.json').write_text(json.dumps(data,indent=2))
elif res==z3.unknown:print('REASON',s.reason_unknown(),flush=True)
print(s.statistics(),flush=True)
