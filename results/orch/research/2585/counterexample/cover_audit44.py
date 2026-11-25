import itertools,json,time
from pathlib import Path
P=L=4;n=P+L;ALL=(1<<(1<<n))-1
inputs=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
checks=0;graphs=0;started=time.monotonic()
for code in range(1<<(P*L)):
 E=[(p,P+l) for p in range(P) for l in range(L) if code>>(p*L+l)&1]
 if any(sum((p,P+l) in E and (q,P+l) in E for l in range(L))>1 for p in range(P) for q in range(p)):continue
 F=0
 for p,l in E:F|=inputs[p]&inputs[l]
 valid=[cm for cm in range(1<<n) if all(cm>>p&1 or cm>>l&1 for p,l in E)]
 for cm in [min(valid,key=int.bit_count)]:
  if any(not(cm>>p&1 or cm>>l&1) for p,l in E):continue
  groups={}
  for p,l in E:
   a,b=(p,l) if cm>>p&1 else (l,p)
   groups.setdefault(a,[]).append(b)
  gates=[];outs=[]
  def gate(op,a,b):gates.append((op,a,b));return n+len(gates)-1
  for a,bs in groups.items():
   acc=bs[0]
   for b in bs[1:]:acc=gate('or',acc,b)
   outs.append(gate('and',a,acc))
  if outs:
   output=outs[0]
   for b in outs[1:]:output=gate('or',output,b)
  else:output=n
  assert len(gates)<=max(0,len(E)+cm.bit_count()-1)
  w=inputs[:]
  for op,a,b in gates:
   assert a<len(w) and b<len(w)
   w.append(w[a]|w[b] if op=='or' else w[a]&w[b])
  assert (w[output] if output<len(w) else 0)==F
  for p,l in E:
   r=[({1} if i==p else {2} if i==l else set()) for i in range(n)]
   for op,a,b in gates:r.append(r[a]|r[b] if op=='or' else {s|t for s in r[a] for t in r[b] if s&t==0})
   assert 3 in r[output]
  checks+=1
 graphs+=1
summary={'graphs':graphs,'cover_cases':checks,'assignments_per_case':1<<n,'read1_verified_for_all_edges':True,'cost_bound':'m + |A| + |B| - 1 (Nat subtraction)','seconds':round(time.monotonic()-started,3)}
print(json.dumps(summary,indent=2))
Path('/tmp/oec/pequalnp-pilot-46/gap-2585/counterexample/cover-audit44.json').write_text(json.dumps(summary,indent=2))
