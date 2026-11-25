import sys,time,json
from pathlib import Path
from itertools import combinations
from datetime import datetime,timezone
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
spec=json.loads(Path(sys.argv[1]).read_text());family=spec['name'];n=spec['n'];m=int(sys.argv[2]);limit=int(sys.argv[3]);mode=sys.argv[4] if len(sys.argv)>4 else 'dirty'
edges=[tuple(e) for e in spec['edges']];colors=spec['colors']
N=[sum(1<<(b if a==i else a) for a,b in edges if i in [a,b]) for i in range(n)]
assert all((N[a]&N[b]).bit_count()<=1 for a in range(n) for b in range(a))
assert all(colors[a]!=colors[b] for a,b in edges)
def target(x):return any(x>>a&1 and x>>b&1 for a,b in edges)
mins=[(1<<a)|(1<<b) for a,b in edges]
maxzeros=[x for x in range(1<<n) if not target(x) and all(x>>i&1 or x&N[i] for i in range(n))]
patterns=sorted(set(mins+maxzeros));width=len(patterns);indexes={x:i for i,x in enumerate(patterns)}
inputs=[sum(1<<j for j,x in enumerate(patterns) if x>>i&1) for i in range(n)]
expected=sum(1<<indexes[x] for x in mins);zeromask=sum(1<<indexes[x] for x in maxzeros)
cover=next(S for k in range(n+1) for S in combinations(range(n),k) if all(a in S or b in S for a,b in edges));tau=len(cover)
s=z3.SolverFor('QF_BV');s.set(timeout=limit);idxwidth=(n+m).bit_length();signals=[z3.BitVecVal(x,width) for x in inputs];below=[z3.BoolVal(False) for i in range(n)];gates=[]
def select(index,values):
 result=values[-1]
 for i in range(len(values)-2,-1,-1):result=z3.If(index==i,values[i],result)
 return result
for i in range(m):
 a=z3.BitVec(f'a{i}',idxwidth);b=z3.BitVec(f'b{i}',idxwidth);op=z3.Bool(f'or{i}');g=z3.BitVec(f'g{i}',width);bf=z3.Bool(f'below{i}')
 s.add(z3.ULT(a,n+i),z3.ULT(b,n+i),z3.ULE(a,b))
 s.add(g==z3.If(op,select(a,signals)|select(b,signals),select(a,signals)&select(b,signals)))
 s.add(bf==(g&z3.BitVecVal(zeromask,width)==0))
 # Every real AO wire is satisfiable. Thus no dirty OR may read a clean operand.
 if mode!='unfixed':s.add(z3.Implies(op,select(a,below)==select(b,below)))
 s.add(g != 0, g != (1 << width)-1)
 s.add(*[g != previous for previous in signals])
 signals.append(g);below.append(bf);gates.append((op,a,b,g,bf))
s.add(signals[-1]==z3.BitVecVal(expected,width))
if mode=='dirty':s.add(z3.Or([z3.And(z3.Not(op),z3.Not(bf)) for op,a,b,g,bf in gates]))
for i in range(m-1):s.add(z3.Or([z3.Or(a==n+i,b==n+i) for op,a,b,g,bf in gates[i+1:]]))
for i in range(1,m):
 op,a,b,g,bf=gates[i];op0,a0,b0,g0,bf0=gates[i-1]
 key=z3.Concat(z3.If(op,z3.BitVecVal(0,1),z3.BitVecVal(1,1)),a,b);key0=z3.Concat(z3.If(op0,z3.BitVecVal(0,1),z3.BitVecVal(1,1)),a0,b0)
 s.add(z3.Or(a==n+i-1,b==n+i-1,z3.ULE(key0,key)))
if mode=='control':
 desc=[];terms=[];pending=set(edges)
 def add(op,a,b):desc.append([op,a,b]);return n+len(desc)-1
 for v in cover:
  es=[e for e in sorted(pending) if v in e]
  if not es:continue
  ns=[b if a==v else a for a,b in es];pending.difference_update(es);z=ns[0]
  for w in ns[1:]:z=add(True,z,w)
  terms.append(add(False,v,z))
 output=terms[0]
 for t in terms[1:]:output=add(True,output,t)
 mapping={i:i for i in range(n)};ordered=[];todo=set(range(len(desc)))
 while todo:
  ready=[]
  for i in todo:
   op,a,b=desc[i]
   if a in mapping and b in mapping:
    aa,bb=sorted([mapping[a],mapping[b]]);ready.append(((0 if op else 1,aa,bb),i,op,aa,bb))
  _,i,op,a,b=min(ready);mapping[n+i]=n+len(ordered);ordered.append([op,a,b]);todo.remove(i)
 assert len(ordered)==m and mapping[output]==n+m-1
 for (op,a,b,g,bf),(cop,ca,cb) in zip(gates,ordered):s.add(op==cop,a==ca,b==cb)
base=Path(f'/tmp/oec/pequalnp-pilot-152/gap-3754/{family}{n}-size{m}-{mode}-minimal')
base.with_suffix('.smt2').write_text(s.to_smt2())
print(datetime.now(timezone.utc).isoformat(),family,n,'edges',len(edges),'tau',tau,'gates',m,'patterns',width,'mode',mode,'liftfixed',mode!='unfixed',flush=True)
start=time.monotonic();res=s.check();print('RESULT',res,'seconds',round(time.monotonic()-start,3),flush=True)
if res==z3.sat:
 mo=s.model();desc=[[bool(z3.is_true(mo.eval(op))),mo.eval(a).as_long(),mo.eval(b).as_long()] for op,a,b,g,bf in gates]
 full=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)];truth=sum(1<<x for x in range(1<<n) if target(x));allbits=(1<<(1<<n))-1;falsebits=allbits^truth
 fullbelow=[False]*n
 for op,a,b in desc:
  f=(full[a]|full[b]) if op else (full[a]&full[b]);full.append(f);fullbelow.append(f&falsebits==0)
 assert full[-1]==truth
 if mode!='unfixed':assert all(not op or fullbelow[a]==fullbelow[b] for op,a,b in desc)
 dirty=[i for i,(op,a,b) in enumerate(desc) if not op and not fullbelow[n+i]]
 if mode=='dirty':assert dirty
 R=set();stack=[n+m-1]
 while stack:
  w=stack.pop()
  if w<n or w-n in R:continue
  R.add(w-n);_,a,b=desc[w-n];stack.extend([a,b])
 assert len(R)==m
 data=dict(n=n,edges=edges,bipartition=colors,gates=[['or' if op else 'and',a,b] for op,a,b in desc],output=n+m-1,dirty_and_indices=dirty,below_gate=fullbelow[n:],cover=list(cover),standard_bound=len(edges)+tau-1)
 print('VERIFIED_FULL_TRUTH_TABLE',json.dumps(data),flush=True);base.with_name(base.name+'-model.json').write_text(json.dumps(data,indent=2))
elif res==z3.unknown:print('REASON',s.reason_unknown(),flush=True)
print(s.statistics(),flush=True)
