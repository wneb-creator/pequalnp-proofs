from pathlib import Path
import sys,json,itertools,time
n,s=10,18
R=1<<n;A=R+n+s+2
p=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
src=Path(sys.argv[1]);dst=Path(sys.argv[2])
model=set()
for line in src.read_text().splitlines():
 if line.startswith('v '):model.update(int(v) for v in line[2:].split() if int(v)>0)
assert model,'no model'
raw=[]
for j in range(s):
 op=next(d for d in range(4) if p(0,j,d) in model)
 a=next(k for k in range(n+j+1) if p(1,j,k) in model)
 b=next(k for k in range(n+j+1) if p(2,j,k) in model)
 raw.append([op,a,b])
truths=[sum(1<<r for r in range(R) if r>>v&1) for v in range(n)]
known={tt:i for i,tt in enumerate(truths)};known[0]=-1
mapped={i:i for i in range(n)};gates=[]
for j,(op,a,b) in enumerate(raw):
 a=mapped.get(a,-1);b=mapped.get(b,-1)
 av=truths[a] if a>=0 else 0;bv=truths[b] if b>=0 else 0
 tt=av&bv if op==0 else av|bv if op==1 else av&~bv if op==2 else ~av&bv
 if tt in known:mapped[n+j]=known[tt]
 else:
  assert a>=0 and b>=0
  q=n+len(gates);gates.append([op,a,b]);truths.append(tt);known[tt]=q;mapped[n+j]=q
out=mapped[n+s-1]
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
target=sum(1<<r for r in range(R) if any((r>>a)&1 and (r>>b)&1 for a,b in edges))
assert out>=0 and truths[out]==target,'signed model does not compute target'
live={out}
for q in range(len(gates)-1,-1,-1):
 if n+q in live:live.update(gates[q][1:])
active=[q for q in range(len(gates)) if n+q in live]
rename={i:i for i in range(n)};small=[]
for q in active:
 op,a,b=gates[q];rename[n+q]=n+len(small);small.append([op,rename[a],rename[b]])
out=rename[out];gates=small;k=len(gates)
start=time.time();best_count=100;best_pol=0;best_mask=0
for pol in range(1<<k):
 needed=0
 for j,(op,a,b) in enumerate(gates):
  pj=(pol>>j)&1
  for wire,neg in [(a,int(op==3)),(b,int(op==2))]:
   pi=(pol>>(wire-n))&1 if wire>=n else 0
   if pi!=(pj^neg):needed |= 1<<wire
 if ((pol>>(out-n))&1 if out>=n else 0):needed|=1<<out
 count=needed.bit_count()
 if count<best_count:best_count=count;best_pol=pol;best_mask=needed
 if count==0:break
actual=[];wires={i:i for i in range(n)};opposites={}
def literal(wire,orientation):
 pi=(best_pol>>(wire-n))&1 if wire>=n else 0
 if orientation==pi:return wires[wire]
 if wire not in opposites:
  actual.append([2,wires[wire],wires[wire]])
  opposites[wire]=n+len(actual)-1
 return opposites[wire]
for j,(op,a,b) in enumerate(gates):
 pj=(best_pol>>j)&1
 av=literal(a,pj^int(op==3));bv=literal(b,pj^int(op==2))
 base=1 if op==1 else 0
 actual.append([base^pj,av,bv]);wires[n+j]=n+len(actual)-1
output=literal(out,0)
if not any(op==2 for op,a,b in actual) and len(actual)<19:actual.append([2,0,0])
assert len(actual)<=k+best_count+1
rows=[];errors=[]
for r in range(R):
 w=[bool(r>>i&1) for i in range(n)]
 for op,a,b in actual:w.append(w[a] and w[b] if op==0 else w[a] or w[b] if op==1 else not w[a])
 got=w[output];want=bool(target>>r&1);rows.append([r,int(got),int(want)])
 if got!=want:errors.append(r)
result={'raw_signed':raw,'reduced_signed':gates,'signed_output':out,'binary_gates':k,'minimum_not_count':best_count,'polarity_bits':best_pol,'orientation_seconds':time.time()-start,'actual_gates':actual,'actual_output':output,'actual_size':len(actual),'actual_not_count':sum(op==2 for op,a,b in actual),'errors':errors,'held_gap_counterexample':not errors and len(actual)<=19 and any(op==2 for op,a,b in actual),'all_rows':rows}
dst.write_text(json.dumps(result,indent=2))
print(json.dumps({key:value for key,value in result.items() if key not in ['all_rows','raw_signed','reduced_signed','actual_gates']}))
