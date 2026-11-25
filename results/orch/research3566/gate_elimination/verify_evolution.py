import argparse,json,itertools
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('source');a=p.parse_args()
data=json.loads(Path(a.source).read_text());record=data.get('witness') or data['best_valid']
n=record.get('inputs',14);gates=record.get('normalized_gates',record['gates']);out=record.get('output',n+len(gates)-1)
edges=[tuple(e) for e in record['edges']];left=set(record.get('left',range(7)));right=set(record.get('right',range(7,n)))
assert all(u in left and v in right for u,v in edges)
assert len(edges)==len(set(edges))
assert all(op in (0,1) and 0<=u<n+i and 0<=v<n+i for i,(op,u,v) in enumerate(gates))
for l1,l2 in itertools.combinations(left,2):
 for r1,r2 in itertools.combinations(right,2):
  assert not all(e in edges for e in ((l1,r1),(l1,r2),(l2,r1),(l2,r2)))
dirty_and=set();pair_dirty_and=set()
for x in range(1<<n):
 wires=[bool((x>>i)&1) for i in range(n)]
 for op,u,v in gates:wires.append(wires[u] and wires[v] if op==0 else wires[u] or wires[v])
 actual=wires[out] if out<len(wires) else False
 expected=any(wires[u] and wires[v] for u,v in edges)
 assert actual==expected,(x,actual,expected)
 if not expected:
  for i,(op,u,v) in enumerate(gates):
   if op==0 and wires[n+i]:
    dirty_and.add(i)
    if x.bit_count()<=2:pair_dirty_and.add(i)
cover=None
for k in range(n+1):
 for S in itertools.combinations(range(n),k):
  S=set(S)
  if all(u in S or v in S for u,v in edges):cover=sorted(S);break
 if cover is not None:break
seen=set();stack=[out]
while stack:
 i=stack.pop()
 if i<n or i in seen:continue
 assert i<n+len(gates);seen.add(i);_,u,v=gates[i-n];stack.extend((u,v))
print(json.dumps({'verified_assignments':1<<n,'edges':len(edges),'minimum_vertex_cover':cover,
 'dirty_and_count':len(dirty_and),'pair_dirty_and_count':len(pair_dirty_and),'used_gates':len(seen),'gain':len(edges)+len(cover)-1-len(seen),'counterexample':len(edges)+len(cover)-1>len(seen)},sort_keys=True))
