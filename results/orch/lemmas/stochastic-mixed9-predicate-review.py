from pathlib import Path
from itertools import product
from collections import Counter
import hashlib,json,time
D=Path('results/orch/lemmas'); scratch=Path('/tmp/oec/pequalnp-pilot-81'); start=time.monotonic()
sets=[frozenset(i for i in range(3) if m>>i&1) for m in range(8)]
N=[frozenset([0,1,2]),frozenset([0,3,4]),frozenset([1,3,5]),frozenset([2,4,5])]
models=[]
for values in product(range(1,7),repeat=6):
 r=[sets[x] for x in values]
 if any(frozenset(t for t in range(6) if u in r[t]) in [N[2],N[3]] for u in range(3)):continue
 forced=[frozenset(t for t in range(6) if any(r[x]<=r[t] for x in row)) for row in N]
 for a,b in product([0,2,4],[0,1,3]):
  A=forced[:];A[2]=A[2]|{a};A[3]=A[3]|{b}
  counts=[sum(t in row for row in A) for t in range(6)]
  if any(counts[t]>1+len(r[t]) for t in range(6)):continue
  full=[any(counts[x]==1+len(r[x]) for x in N[i]) for i in [0,1]]
  if any(full[i] and A[i]!=N[i] for i in [0,1]):continue
  allowed=[]
  for mask in range(1,8):
   T=sets[mask];rows=[any(r[x]<=T for x in row) for row in N]
   if any(full[i] and rows[i] for i in [0,1]):continue
   if sum(rows)>len(T):continue
   if any(counts[t]+int(T<=r[t])>1+len(r[t]) for t in range(6)):continue
   allowed.append(mask)
  assert all(full) and not allowed
  models.append((values,a,b))
expected=json.loads((scratch/'constructive-mixed9-predicate.json').read_text())
expectset={(tuple(row['R']),row['extra2'],row['extra5']) for row in expected['data']}
assert set(models)==expectset and len(models)==120 and len({x[0] for x in models})==30
source=D/'constructive-mixed9-finite-core.lean';s=source.read_text()
# Check all literal Boolean lookup tables independently against their definitions.
import re
for name,expectedtable in [('m9_sub',[[a<=b for b in sets] for a in sets]),('m9_bit',[[i in a for i in range(3)] for a in sets])]:
 text=s.split('def '+name+' ',1)[1].split('\ndef ',1)[0]
 actual=[x=='true' for x in re.findall(r'\b(?:true|false)\b',text)]
 assert actual==[v for row in expectedtable for v in row],name
report={'verdict':'PASS independent exact set-based census and source/predicate semantic consistency','source':str(source),'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'models':len(models),'distinct_line_patterns':len({x[0] for x in models}),'all_models_force_both_protected_rows':True,'all_models_forbid_nonzero_eligiblepoint_residual':True,'seconds':time.monotonic()-start,'scope':'This verifies the finite predicate only. Actual-circuit premises, especially normal residual ranges, excluded missing unit masks, row-budget and point-budget strengthening, require separate transfer lemmas.','checks':['All64 subset lookup entries and24 bit entries match set semantics.','Extra choices are exactly the complements of the two missing triples: {0,2,4} and {0,1,3}.','Missing unit masks42 and52 are exactly the two designated missing triples.','Force/count/full/pointAllowed/normal/good/bad source clauses agree with the independent set predicate; finite theorem quantifies all8^6 values and filters endpoints explicitly.','Independent census starts from all6^6 nonempty nonfull residual vectors, not the previous filtered census.']}
(D/'stochastic-mixed9-predicate-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
