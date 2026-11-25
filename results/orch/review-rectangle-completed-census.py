from pathlib import Path
from collections import defaultdict
import gzip, hashlib, json, time, sys
p=Path(sys.argv[1]); output=Path(sys.argv[2]); start=time.monotonic()
manifest=json.loads((p/'manifest.json').read_text())
for entry in manifest:
 q=p/entry['file']; assert q.stat().st_size==entry['bytes']
 assert hashlib.sha256(q.read_bytes()).hexdigest()==entry['sha256'],entry['file']
weights=json.loads((p/'weights.json').read_text())
profiles=json.loads(gzip.decompress((p/'profiles.json.gz').read_bytes()))
kept=json.loads(gzip.decompress((p/'maximal-profiles.json.gz').read_bytes()))
for w in weights:
 assert len(w['weights'])==w['rows']
 assert all(len(row)==w['cols'] for row in w['weights'])
 assert sum(map(sum,w['weights']))==w['total']

def exact_max(w,p_mask,n_mask):
 rows=[i for i in range(w['rows']) if p_mask>>i&1]
 cols=[j for j in range(w['cols']) if n_mask>>j&1]
 if not rows or not cols:return 0,0
 if len(rows)<=len(cols):vectors=[tuple(w['weights'][i][j] for j in cols) for i in rows]
 else:vectors=[tuple(w['weights'][i][j] for i in rows) for j in cols]
 sums=[(0,)*len(vectors[0])];best=0
 for mask in range(1,1<<len(vectors)):
  bit=mask&-mask;prior=sums[mask^bit];v=vectors[bit.bit_length()-1]
  total=tuple(x+y for x,y in zip(prior,v));sums.append(total)
  best=max(best,sum(x for x in total if x>0))
 return best,1<<len(vectors)

subsets=0
for i,r in enumerate(profiles):
 w=weights[r['weight']];assert 0<=r['positive_mask']<1<<w['rows'];assert 0<=r['negative_false_mask']<1<<w['cols']
 cost,amount=exact_max(w,r['positive_mask'],r['negative_false_mask']);subsets+=amount
 assert cost==r['cost'],(i,cost,r)
 if i%10000==0:print(json.dumps({'checked_profiles':i+1,'seconds':time.monotonic()-start}),flush=True)
groups=defaultdict(list)
for r in kept:groups[r['weight'],r['cost']].append((r['positive_mask'],r['negative_false_mask']))
nontrivial=0
for r in profiles:
 a,b=r['positive_mask'],r['negative_false_mask']
 if not a or not b:continue
 nontrivial+=1
 assert any(a&aa==a and b&bb==b for aa,bb in groups[r['weight'],r['cost']]),r
result={'verdict':'PASS','manifest_sha256':hashlib.sha256((p/'manifest.json').read_bytes()).hexdigest(),'manifest_entries':len(manifest),'weight_arrays':len(weights),'profiles_exactly_recomputed':len(profiles),'subset_options':subsets,'nontrivial_profiles':nontrivial,'dominating_profiles':len(kept),'seconds':time.monotonic()-start,'scope':'Independent Python integer maximum computation and containment verification; no Lean or whole-search claim.'}
output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
