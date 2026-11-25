import sys,json,time
from pathlib import Path
from itertools import combinations,permutations,product
from datetime import datetime,timezone
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
spec=json.loads(Path(sys.argv[1]).read_text());n=spec['n'];edges=[tuple(e) for e in spec['edges']];colors=spec['colors'];name=spec['name']
m=int(sys.argv[2]);q=int(sys.argv[3]);limit=int(sys.argv[4]);p=m-2*q;L=p+1
assert q>=1 and p>=0
neighbors=[set() for _ in range(n)]
for a,b in edges:neighbors[a].add(b);neighbors[b].add(a);assert colors[a]!=colors[b]
assert all(len(neighbors[a]&neighbors[b])<=1 for a in range(n) for b in range(a))
def target(x):return any(x>>a&1 and x>>b&1 for a,b in edges)
mins=sorted({(1<<a)|(1<<b) for a,b in edges})
maxzeros=[x for x in range(1<<n) if not target(x) and all(x>>i&1 or target(x|(1<<i)) for i in range(n))]
patterns=sorted(set(mins+maxzeros));width=len(patterns);indices={x:i for i,x in enumerate(patterns)}
expected=sum(1<<indices[x] for x in mins);falsemask=sum(1<<indices[x] for x in maxzeros)
s=z3.SolverFor('QF_BV');s.set(timeout=limit);iw=(n+m).bit_length()
signals=[z3.BitVecVal(sum(1<<j for j,x in enumerate(patterns) if x>>i&1),width) for i in range(n)];prefix=[];terminal=[]
def select(i,vals):
 result=vals[-1]
 for j in range(len(vals)-2,-1,-1):result=z3.If(i==j,vals[j],result)
 return result
def union(vals):
 result=z3.BitVecVal(0,width)
 for v in vals:result=result|v
 return result
for i in range(L):
 a=z3.BitVec('a'+str(i),iw);b=z3.BitVec('b'+str(i),iw);op=z3.Bool('or'+str(i));g=z3.BitVec('g'+str(i),width)
 s.add(z3.ULT(a,n+i),z3.ULT(b,n+i),z3.ULE(a,b))
 s.add(g==z3.If(op,select(a,signals)|select(b,signals),select(a,signals)&select(b,signals)))
 s.add(g&falsemask!=0,g!=0,g!=(1<<width)-1,*[g!=v for v in signals])
 signals.append(g);prefix.append((op,a,b,g))
s.add(z3.PbEq([(z3.Not(op),1) for op,a,b,g in prefix],1))
for i in range(1,L):
 op,a,b,g=prefix[i];op0,a0,b0,g0=prefix[i-1]
 key=z3.Concat(z3.If(op,z3.BitVecVal(0,1),z3.BitVecVal(1,1)),a,b);key0=z3.Concat(z3.If(op0,z3.BitVecVal(0,1),z3.BitVecVal(1,1)),a0,b0)
 s.add(z3.Or(a==n+i-1,b==n+i-1,z3.ULE(key0,key)))
for i in range(q):
 a=z3.BitVec('ta'+str(i),iw);b=z3.BitVec('tb'+str(i),iw);g=z3.BitVec('tg'+str(i),width)
 s.add(z3.ULT(a,n+L),z3.ULT(b,n+L),z3.ULE(a,b),g==select(a,signals)&select(b,signals),g&falsemask==0)
 if terminal:s.add(z3.ULT(z3.Concat(terminal[-1][0],terminal[-1][1]),z3.Concat(a,b)))
 terminal.append((a,b,g))
s.add(union([g for a,b,g in terminal])==expected)
for i,(a,b,g) in enumerate(terminal):s.add(g&~union([h for j,(c,d,h) in enumerate(terminal) if i!=j])!=0)
for fault in range(L):
 altered=signals[:n+fault]+[z3.BitVecVal(0,width)]
 for op,a,b,g in prefix[fault+1:]:altered.append(z3.If(op,select(a,altered)|select(b,altered),select(a,altered)&select(b,altered)))
 s.add(union([select(a,altered)&select(b,altered) for a,b,g in terminal])!=expected)
degrees=[len(v) for v in neighbors];classes=[[v for v in range(n) if degrees[v]==d] for d in sorted(set(degrees))];edge_set={tuple(sorted(e)) for e in edges};autos=[]
if name=='cycle':candidates=([((offset+sign*v)%n) for v in range(n)] for offset in range(n) for sign in [-1,1])
else:
 assert n<=10
 def candidates_from_classes():
  for images in product(*[list(permutations(cls)) for cls in classes]):
   perm=list(range(n))
   for cls,image in zip(classes,images):
    for a,b in zip(cls,image):perm[a]=b
   yield perm
 candidates=candidates_from_classes()
for perm in candidates:
 if {tuple(sorted((perm[a],perm[b]))) for a,b in edges}==edge_set:autos.append(perm)
reps=sorted({min(tuple(sorted((perm[a],perm[b]))) for perm in autos) for a in range(n) for b in range(a,n)})
s.add(z3.Or([z3.And(prefix[0][1]==a,prefix[0][2]==b) for a,b in reps]))
base=Path('/tmp/oec/pequalnp-pilot-152/gap-3754')/(name+str(n)+'-size'+str(m)+'-one-normal-q'+str(q))
base.with_suffix('.smt2').write_text(s.to_smt2())
print(datetime.now(timezone.utc).isoformat(),name,n,'size',m,'prefixORs',p,'cleanANDs',q,'samples',width,'maxfalse',len(maxzeros),'autos',len(autos),flush=True)
start=time.monotonic();res=s.check();print('RESULT',res,'seconds',round(time.monotonic()-start,3),flush=True)
if res==z3.sat:
 model=s.model();gates=[['or' if z3.is_true(model.eval(op)) else 'and',model.eval(a).as_long(),model.eval(b).as_long()] for op,a,b,g in prefix]
 gates += [['and',model.eval(a).as_long(),model.eval(b).as_long()] for a,b,g in terminal]
 output=n+L
 for i in range(1,q):gates.append(['or',*sorted([output,n+L+i])]);output=n+len(gates)-1
 assert len(gates)==m and output==n+m-1
 values=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)];F=sum(1<<x for x in range(1<<n) if target(x));fullmask=(1<<(1<<n))-1
 for i,(op,a,b) in enumerate(gates):
  assert 0<=a<n+i and 0<=b<n+i
  values.append(values[a]|values[b] if op=='or' else values[a]&values[b])
 assert values[-1]==F
 below=[v&(fullmask^F)==0 for v in values];dirty=[i for i,(op,a,b) in enumerate(gates) if op=='and' and not below[n+i]]
 assert len(dirty)==1
 assert all(op!='or' or below[a]==below[b] for op,a,b in gates)
 for fault in range(m):
  changed=values[:n]
  for i,(op,a,b) in enumerate(gates):changed.append(0 if i==fault else (changed[a]|changed[b] if op=='or' else changed[a]&changed[b]))
  assert any(not(changed[-1]>>x&1) for x in mins)
 cover=next(S for k in range(n+1) for S in combinations(range(n),k) if all(a in S or b in S for a,b in edges))
 data=dict(n=n,edges=edges,bipartition=colors,gates=gates,output=output,dirty_and_indices=dirty,below_gate=below[n:],cover=list(cover),standard_bound=len(edges)+len(cover)-1,clean_ands=q)
 base.with_name(base.name+'-model.json').write_text(json.dumps(data,indent=2));print('VERIFIED_FULL_TRUTH_TABLE',json.dumps(data),flush=True)
elif res==z3.unknown:print('REASON',s.reason_unknown(),flush=True)
print(s.statistics(),flush=True)
