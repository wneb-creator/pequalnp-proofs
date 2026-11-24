import json
from pathlib import Path
ROOT=Path('/tmp/oec/pequalnp-pilot-21/lower-bound')
LINES=[{(w+p)%13 for p in (0,1,3,9)} for w in range(13)]
L,M=LINES[0],LINES[1]
X=sorted(set(range(13))-(L|M))
A=sorted(M-L); B=sorted(L-M)
a1,b1=A[0],B[0]
net=[]
def gate(op,a,b):
 assert a!=b and 0<=a<13+len(net) and 0<=b<13+len(net)
 net.append([op,a,b]); return 12+len(net)
def fold(op,indices):
 indices=list(indices); value=indices[0]
 for i in indices[1:]: value=gate(op,value,i)
 return value
cx=fold('and',X)
a2=fold('and',A[1:]); b2=fold('and',B[1:])
u=gate('or',a1,b2);v=gate('or',a2,b1)
w=gate('and',u,v); cross=gate('and',a1,b1); guarded=gate('or',cx,cross); shared=gate('and',guarded,w)
router_gates=len(net)
outputs=[]
for i,line in enumerate(LINES):
 out=fold('or',sorted(line))
 if i in (0,1):out=gate('or',out,shared)
 outputs.append(out)
def evaluate(mask):
 values=[bool(mask&(1<<p)) for p in range(13)]
 for op,a,b in net:values.append((values[a] and values[b]) if op=='and' else (values[a] or values[b]))
 return values
band=[r for r in range(8192) if r.bit_count() in (7,8)]
errors=[]
seen=[set() for _ in net]
seen7=[set() for _ in net]; seen8=[set() for _ in net]
for row in band:
 values=evaluate(row)
 expected=[any(row&(1<<p) for p in line) for line in LINES]
 if [values[o] for o in outputs]!=expected:errors.append(row)
 for j in range(len(net)):
  seen[j].add(values[13+j])
  (seen7 if row.bit_count()==7 else seen8)[j].add(values[13+j])
assert not errors and all(s=={False,True} for s in seen)
assert all(True in s for s in seen7) and all(False in s for s in seen8)
complements=[sum(1<<p for p in range(13) if p not in LINES[i]) for i in (0,1)]
for mask in complements:
 assert evaluate(mask)[shared]
 assert all(not evaluate(mask^(1<<p))[shared] for p in range(13) if mask&(1<<p))
first=[]
for mask in complements:
 candidates=[]
 for j in range(len(net)):
  if evaluate(mask)[13+j] and all(not evaluate(mask^(1<<p))[13+j] for p in range(13) if mask&(1<<p)):
   candidates.append(13+j)
 first.append(min(candidates))
assert first==[shared,shared]
minterms=[]
for mask in range(8192):
 if evaluate(mask)[shared] and all(not evaluate(mask^(1<<p))[shared] for p in range(13) if mask&(1<<p)):
  minterms.append(mask)
assert sorted(m.bit_count() for m in minterms)==[2,9,9,10]
result={'scope':'Auxiliary mixed certificate-routing obstruction, not a counterexample to the39-gate statement.',
 'gate_count':len(net),'router_gate_count':router_gates,'router_and_count':sum(op=='and' for op,_,_ in net[:router_gates]),
 'lines':[sorted(L),sorted(M)],'common_outside':X,'exclusive_A':A,'exclusive_B':B,
 'gates':net,'outputs':outputs,'shared_gate':shared,'same_first_complement_certificate_gate':first,
 'shared_minterms':minterms,'shared_minterm_sizes':[m.bit_count() for m in minterms],
 'band_rows_checked':len(band),'band_errors':errors,'all_gates_band_nonconstant':True,'all_gates_true_on_some7_false_on_some8':True,
 'shared_band_positive_rows':[r for r in band if evaluate(r)[shared]],'lean_checked':False}
(ROOT/'mixed-complement-router-endpoints.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['scope','gate_count','router_gate_count','router_and_count','same_first_complement_certificate_gate','shared_minterm_sizes','band_rows_checked','band_errors','all_gates_band_nonconstant','all_gates_true_on_some7_false_on_some8']}))
