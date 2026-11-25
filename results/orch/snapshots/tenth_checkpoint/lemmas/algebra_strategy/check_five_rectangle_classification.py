"""Independent allowed-pair-only rectangle census; computational companion to Lean."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
case=json.loads((HERE/'five-owner-raw-packet.json').read_text())[0]
census=json.loads((HERE.parent/'reduction_analysis/five_owner_pair_extension_census.json').read_text())
edges=set(map(tuple,case['edges']))
allowed=edges|{tuple(x['local']) for x in census['five_and_dirty_pair_exceptions']}
allowed|={(b,a) for a,b in allowed}
adj=[sum(1<<v for v in range(16) if (u,v) in allowed) for u in range(16)]
records=[];best=0;viable=0
for left in range(1,65536):
 common=65535
 for i in range(16):
  if left>>i&1:common&=adj[i]
 upper=sum(bool((left>>a&1 and common>>b&1)or(left>>b&1 and common>>a&1)) for a,b in edges)
 if upper<4:continue
 right=common
 while right:
  if left<right:
   viable+=1
   count=sum(bool((left>>a&1 and right>>b&1)or(left>>b&1 and right>>a&1)) for a,b in edges)
   if count>=4:
    records.append(dict(left=[i for i in range(16) if left>>i&1],right=[i for i in range(16) if right>>i&1],positive_edges=count))
    best=max(best,count)
  right=(right-1)&common
expected=json.loads((HERE.parent/'reduction_analysis/five_owner_all_and_rectangles.json').read_text())['rectangles_with_at_least_four_edges']
assert records==[{k:r[k] for k in ['left','right','positive_edges']} for r in expected]
assert best==4 and len(records)==9
report=dict(scope='AllAllowed alone; no activation-count hypothesis; computational companion only',left_subsets=65535,viable_right_subsets=viable,maximum=best,shapes=records)
(HERE/'five-rectangle-classification-independent.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
