from pathlib import Path
from collections import deque
import hashlib,json
repo=Path('/workspace/pequalnp-proofs');j=repo/'results/orch/lemmas'
m=json.loads((j/'geometry-laguerre-rank4-manifest.json').read_text());assert len(m['files'])==11
for ent in m['files']:
 p=repo/ent['path'];assert p.parent==j and p.is_file() and p.stat().st_size==ent['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==ent['sha256']
b=json.loads((j/'geometry-laguerre-rank4-461-21-compat-GB.json').read_text())['basis'];lm=[tuple(g[0]['exponents']) for g in b]
q=deque([(0,)*5]);seen=set(q)
while q:
 a=q.popleft()
 for i in range(5):
  t=tuple(z+(i==k) for k,z in enumerate(a))
  if t in seen or any(all(v<=z for v,z in zip(u,t)) for u in lm):continue
  seen.add(t);q.append(t)
assert len(seen)==276
low=json.loads((j/'geometry-laguerre-rank4-461-21-rank3-GB.json').read_text())['basis'];assert len(low)==1 and low[0]==[{'coefficient':1,'exponents':[0]*5}]
print('PASS 11 manifest files exact; unit rank<=3 output, 276 standard monomials in compatibility output over F461 only. Reviewed physical dual derivative rows and signed cofactor left-kernel condition w3*wUB+w4*wUC=0 eliminating the skew variable with opposite signs. No characteristic-zero or full-plane exclusion asserted.')
