from pathlib import Path
import json
from encode import EDGES

P=Path(__file__).resolve().parent
adj={tuple(sorted(e)) for e in EDGES}
independent={2,4,5,6}
private={0:2,1:3,3:4,8:5,7:6,9:7,2:8,4:10,5:12,6:14}
codes={v:{0 if v in independent else 1,private[v]} for v in range(10)}
assert all(1<=len(w)<=2 for w in codes.values())
assert all(all((p^1) not in w for p in w) for w in codes.values())
assert all(any((p^1) in codes[v] for p in codes[u]) for u,v in EDGES)
assert all(not codes[x].issubset(codes[a]|codes[b]) for x in range(10) for a in range(10) for b in range(a,10) if x!=a and x!=b and (a,b) not in adj)
assert all(private[v] not in codes[u] for v in range(10) for u in range(10) if u!=v)
active=sorted(set().union(*codes.values()))
covered=[(u,v) for u in range(10) for v in range(u+1,10) if any((p^1) in codes[v] for p in codes[u])]
result={'codes':{str(v):sorted(w) for v,w in codes.items()},'involution':'p xor1','active_slots':active,'nonempty_positions':len(active),'memberships':sum(map(len,codes.values())),'pair_ids':len({p//2 for p in active}),'covered_actual_edges':[list(e) for e in sorted(adj)],'false_positive_pairs':[list(e) for e in covered if e not in adj],'note':'This satisfies the proposed abstract code constraints only; it is NOT a Boolean circuit or a refutation of the leased statement.'}
(P/'code_model.json').write_text(json.dumps(result,indent=2)+'\n')
print('ABSTRACT MODEL VERIFIED',len(active),'nonempty slots',result['memberships'],'memberships',result['pair_ids'],'pair IDs','false positive pairs',len(result['false_positive_pairs']))
for v in range(10):print(v,sorted(codes[v]))
