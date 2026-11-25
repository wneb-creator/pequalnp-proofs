from itertools import combinations
from collections import Counter
import json, time
n=4
inputs=tuple(sum(((x>>j)&1)<<x for x in range(1<<n)) for j in range(n))
edges=list(combinations(range(n),2))
def good(es):
 s={frozenset(e) for e in es}
 for a,b,c in combinations(range(n),3):
  if all(frozenset(e) in s for e in [(a,b),(b,c),(c,a)]):return False
 for a,b,c,d in __import__('itertools').permutations(range(n),4):
  if all(frozenset(e) in s for e in [(a,b),(b,c),(c,d),(d,a)]):return False
 return True
def target(es):
 return sum(any((x>>a&1) and (x>>b&1) for a,b in es)<<x for x in range(1<<n))
targets={target(es):es for m in range(1<<len(edges)) if good(es:=[e for i,e in enumerate(edges) if m>>i&1])}
found={0:(0,[])}
states={tuple(sorted(inputs)):[]}
print('targets',len(targets),flush=True)
for k in range(1,5):
 nxt={}
 for vals,gs in states.items():
  for a,b in combinations(vals,2):
   for op,c in [('and',a&b),('or',a|b)]:
    if c in vals:continue
    nvals=tuple(sorted((*vals,c)))
    if nvals in nxt:continue
    ngs=gs+[(op,a,b,c)]
    nxt[nvals]=ngs
    if c in targets and c not in found:
     found[c]=(k,ngs)
 print('level',k,'states',len(nxt),'targets found',len(found),flush=True)
 states=nxt
 if len(found)==len(targets):break

def profile(es,gs):
 cones=[]; val_to_gate={}; bad=[]
 for j,(op,a,b,c) in enumerate(gs):
  cone=set()
  for v in [a,b]:
   if v in val_to_gate:
    i=val_to_gate[v]; cone.add(i);cone.update(cones[i])
  cones.append(cone);val_to_gate[c]=j
  owned=[]
  if op=='and':
   for u,v in es:
    x=(1<<u)|(1<<v)
    if c>>x&1 and all(gs[i][0]!='and' or not(gs[i][3]>>x&1) for i in cone):owned.append((u,v))
   if owned and not any(all(t in e for e in owned) for t in range(n)):bad.append((j,owned))
 return bad
results=[]
for t,es in targets.items():
 k,gs=found[t]
 bad=profile(es,gs)
 cover=min(s.bit_count() for s in range(1<<n) if all(s>>a&1 or s>>b&1 for a,b in es))
 results.append({'edges':es,'minimum':k,'star_witness':not bad,'bad_gates':bad,'star_cover_bound':len(es)+cover-1 if es else 0,'gates':gs})
print('minimum counts',dict(Counter(r['minimum'] for r in results)),flush=True)
print('nonstar witnesses',[r for r in results if not r['star_witness']],flush=True)
print('cover mismatch',[r for r in results if r['minimum']!=r['star_cover_bound']],flush=True)
with open('/tmp/oec/pequalnp-pilot-74/star-small-results.json','w') as f:json.dump(results,f,indent=2)
