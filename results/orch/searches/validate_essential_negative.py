import json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-86/counterexample')
d=json.loads((base/'essential-negative-without.verified.json').read_text())
gates=d['gates']; n=d['n']; failures=[]
for forced in range(len(gates)):
 essential=False
 for a,b in d['edges']:
  vals=[i in [a,b] for i in range(n)]
  for j,(u,v,o) in enumerate(gates):vals.append(False if j==forced else (vals[u] or vals[v] if o else vals[u] and vals[v]))
  essential|=not vals[-1]
 if not essential:failures.append(forced)
assert len(failures)==4
print('Exactly four locally incomparable, edge-active OR gates lack any essential edge:',failures)
