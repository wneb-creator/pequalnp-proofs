import json
from pathlib import Path
n=8
c=0; d=4
AA=[1,2,3];BB=[5,6,7]
edges=[(c,b) for b in BB]+[(a,d) for a in AA]+list(zip(AA,BB))
full=(1<<(1<<n))-1
values=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
F=0
for a,b in edges:F|=values[a]&values[b]
N=[0]*n
for a,b in edges:N[a]|=1<<b;N[b]|=1<<a
gates=[];or_reach=[1<<i for i in range(n)]
def add(op,a,b):
 w=len(values);v=(values[a]|values[b]) if op=='or' else (values[a]&values[b])
 values.append(v);gates.append((op,a,b));or_reach.append(or_reach[a]|or_reach[b] if op=='or' else 0)
 return w

def side(A,B):
 roots=[]
 for i in range(3):
  j=(i+1)%3;k=(i+2)%3
  q=add('or',B[j],B[k])
  s=add('or',B[i],B[j])
  h=add('and',A[i],s)
  roots.append(add('or',q,h))
 return add('and',add('and',roots[0],roots[1]),roots[2])
f=side(AA,BB);g=side(BB,AA)
allB=add('or',add('or',BB[0],BB[1]),BB[2])
allA=add('or',add('or',AA[0],AA[1]),AA[2])
starwitness=[add('or',d,b) for b in BB]
U=[(f,g),(c,allB),(d,allA)]
independent=full^F
andchecks=[];orchecks=[]
for j,(op,a,b) in enumerate(gates):
 w=n+j;v=values[w]
 if op=='and':andchecks.append(bool(v&independent))
 else:
  support=[i for i in range(n) if v>>(1<<i)&1]
  centers=[i for i in range(n) if len(support)>=2 and not(v>>(((1<<n)-1)^N[i])&1)]
  orchecks.append(dict(wire=w,support=support,eligible_centers=centers,raw_or_inputs=[i for i in range(n) if or_reach[w]>>i&1]))
pairvalues=[values[a]&values[b] for a,b in U]
covered=0
for v in pairvalues:covered|=v
covers=[s for s in range(1<<n) if all((s>>a&1)or(s>>b&1) for a,b in edges)]
tau=min(s.bit_count() for s in covers)
matching=[(c,5),(1,d),(2,6),(3,7)]
report=dict(vertices=n,edges=edges,gates=gates,U=U,gate_count=len(gates),and_count=len(andchecks),or_count=len(orchecks),eligible_or_count=sum(bool(z['eligible_centers']) for z in orchecks),B=sum(not z['eligible_centers'] for z in orchecks),tau=tau,U_card=len(U),matching=matching,all_AND_dirty=all(andchecks),all_pairs_sound=all(not(v&independent) for v in pairvalues),pairs_cover_exactly_F=covered==F,all_OR_raw_reach_monochromatic=all(all(i<4 for i in z['raw_or_inputs']) or all(i>=4 for i in z['raw_or_inputs']) for z in orchecks),star_witness_wires=dict(allB=allB,allA=allA,matching=starwitness),or_details=orchecks)
assert report['all_AND_dirty'] and report['all_pairs_sound'] and report['pairs_cover_exactly_F']
assert report['B']==0 and tau==4 and len(U)==3
assert report['all_OR_raw_reach_monochromatic']
print(json.dumps(report,indent=2))
