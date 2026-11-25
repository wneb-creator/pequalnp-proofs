import itertools
import json
from pathlib import Path

root=Path('/tmp/oec/pequalnp-pilot-73/counterexample')
data=json.loads((root/'promises.json').read_text())
points=[0,1,3,9]
def parts(xs):
    if not xs:
        yield []
    else:
        x,*rest=xs
        for p in parts(rest):
            yield [frozenset([x])]+p
            for i in range(len(p)):
                yield p[:i]+[p[i]|{x}]+p[i+1:]
partitions=list(parts(list(range(4))))
def bad(p):
    out=set()
    for group in p:
        neigh=0
        for i in group: neigh|=data['lines_through'][points[i]]
        for i in group:
            for l in range(13):
                if neigh>>l&1 and not (data['lines_through'][points[i]]>>l&1): out.add((points[i],l))
    return out
def orcost(targets,n):
    singles={1<<i for i in range(n)}
    targets=set(targets)-singles
    if not targets: return 0,[]
    candidates=[m for m in range(1,1<<n) if m not in singles|targets and any(m&t==m for t in targets)]
    def works(extra):
        known=set(singles)
        for m in sorted(targets|set(extra),key=int.bit_count):
            if not any(a|b==m for a in known for b in known): return False
            known.add(m)
        return True
    for k in range(len(candidates)+1):
        for extra in itertools.combinations(candidates,k):
            if works(extra): return len(targets)+k,list(extra)
    raise AssertionError
results=[]
for i,p in enumerate(partitions):
    for j,q in enumerate(partitions):
        if i>=j or bad(p)&bad(q): continue
        groups=set(p)|set(q)
        point_targets=[sum(1<<k for k in g) for g in groups]
        line_targets=[1+sum(1<<(k+1) for k in g) for g in groups]
        pc,px=orcost(point_targets,4)
        lc,lx=orcost(line_targets,5)
        cost=44+8+pc+lc+2*len(groups)+1
        results.append({'P':[sorted(g) for g in p],'Q':[sorted(g) for g in q],
                        'point_OR_cost':pc,'block_OR_cost':lc,'AND_term_count':len(groups),
                        'total_gates':cost,'point_extras':px,'line_extras':lx})
results.sort(key=lambda x:x['total_gates'])
(root/'partition-results.json').write_text(json.dumps(results,indent=2))
print('partitions',len(partitions),'valid distinct pairs',len(results))
print('best',results[0])
print('cost census', {n:sum(r['total_gates']==n for r in results) for n in sorted({r['total_gates'] for r in results})})
