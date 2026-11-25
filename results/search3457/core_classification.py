"""Exhaustive finite graph census, not a Lean proof or circuit search."""
import itertools,json,time
from collections import Counter,deque
from pathlib import Path
start=time.monotonic()
counts=Counter()
examples={}
matrices=0
for rows in itertools.product(range(16),repeat=4):
    if any((rows[i]&rows[j]).bit_count()>1 for i in range(4) for j in range(i)):
        continue
    matrices+=1
    adj=[set() for _ in range(8)]
    for p,row in enumerate(rows):
        for l in range(4):
            if row>>l&1:
                adj[p].add(4+l)
                adj[4+l].add(p)
    alive=set(range(8))
    queue=deque(v for v in alive if len(adj[v])<2)
    while queue:
        v=queue.popleft()
        if v not in alive:
            continue
        alive.remove(v)
        for w in tuple(adj[v]):
            adj[w].remove(v)
            if len(adj[w])<2:
                queue.append(w)
        adj[v].clear()
    degrees=sorted(len(adj[v]) for v in alive)
    if not alive:
        kind='empty'
    elif len(alive)==6 and degrees==[2]*6:
        kind='C6'
    elif len(alive)==8 and degrees==[2]*8:
        kind='C8'
    elif len(alive)==8 and degrees==[2]*6+[3]*2:
        ends=[v for v in alive if len(adj[v])==3]
        assert (ends[0]<4)!=(ends[1]<4)
        assert ends[1] not in adj[ends[0]]
        paths=[]
        for w in adj[ends[0]]:
            path=[ends[0],w]
            while path[-1]!=ends[1]:
                ns=adj[path[-1]]-{path[-2]}
                assert len(ns)==1
                path.append(next(iter(ns)))
            paths.append(path)
        assert sorted(map(len,paths))==[4,4,4]
        kind='theta333'
    else:
        raise AssertionError((rows,alive,degrees))
    counts[kind]+=1
    examples.setdefault(kind,sum(row<<(4*i) for i,row in enumerate(rows)))
result={'matrix_count':matrices,'core_counts':dict(counts),'example_masks':examples,'elapsed_seconds':time.monotonic()-start,'status':'exhaustive finite graph census; not Lean checked; no circuit bound'}
Path('results/search3457/core_classification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
