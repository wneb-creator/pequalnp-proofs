import itertools
import json
import sys


source = json.load(open(sys.argv[1]))
cuts = json.load(open(sys.argv[2]))
n = source['n']
old = {(1 << u) | (1 << v) for u,v in source['edges']}


def vertices(mask):
    return [i for i in range(n) if mask >> i & 1]


def graph_info(es):
    pairs = [vertices(e) for e in sorted(es)]
    adj = [[False]*n for _ in range(n)]
    for u,v in pairs:
        adj[u][v] = adj[v][u] = True
    for four in itertools.combinations(range(n),4):
        a = four[0]
        for b,c,d in itertools.permutations(four[1:]):
            assert not (adj[a][b] and adj[b][c] and adj[c][d] and adj[d][a])
    independent = [m for m in range(1 << n)
                   if all(not (m >> u & 1 and m >> v & 1) for u,v in pairs)]
    alpha = max(m.bit_count() for m in independent)
    maximal = [m for m in independent if all(
        any(adj[u][v] and m >> v & 1 for v in range(n))
        for u in range(n) if not m >> u & 1)]
    return pairs,adj,n-alpha,maximal


def isomorphic(a,b):
    da = [sum(row) for row in a]
    db = [sum(row) for row in b]
    if sorted(da) != sorted(db):
        return False
    sa = [(da[u],tuple(sorted(da[v] for v in range(n) if a[u][v]))) for u in range(n)]
    sb = [(db[u],tuple(sorted(db[v] for v in range(n) if b[u][v]))) for u in range(n)]
    allowed = [[v for v in range(n) if sb[v]==sa[u]] for u in range(n)]
    mapping = {}
    used = set()

    def visit():
        if len(mapping) == n:
            return True
        possibilities = []
        for u in range(n):
            if u in mapping:
                continue
            choices = [v for v in allowed[u] if v not in used and all(
                a[u][p] == b[v][q] for p,q in mapping.items())]
            if not choices:
                return False
            possibilities.append((len(choices),u,choices))
        _,u,choices = min(possibilities)
        for v in choices:
            mapping[u] = v
            used.add(v)
            if visit():
                return True
            used.remove(v)
            del mapping[u]
        return False

    return visit()


records = []
classes = []
for i,r in enumerate(cuts):
    if r['maximum_bound'] != 19:
        continue
    es = (old-set(r['best']['deleted'])) | set(r['added'])
    pairs,adj,tau,mis = graph_info(es)
    assert len(es)==14 and tau==6
    record = dict(id=f'edited-{i}',n=n,edges=pairs,tau=tau,bound=19,target_gates=18,
                  added=[vertices(e) for e in r['added']],
                  deleted=[vertices(e) for e in r['best']['deleted']],
                  maximal_independent_sets=[vertices(m) for m in mis],
                  maximal_independent_count=len(mis))
    ci = next((j for j,(_,other) in enumerate(classes) if isomorphic(adj,other)),None)
    if ci is None:
        ci = len(classes)
        classes.append((record,adj))
    record['isomorphism_class'] = ci
    records.append(record)
representatives = [r for r,_ in classes]
representatives.sort(key=lambda r:r['maximal_independent_count'])
result = dict(graph_count=len(records),isomorphism_classes=len(classes),
              graphs=records,representatives=representatives,
              validation='C4 checked by explicit four-vertex cycles; tau independently by all subsets.')
with open(sys.argv[3],'w') as f:
    json.dump(result,f,indent=2)
print(json.dumps(dict(graph_count=len(records),isomorphism_classes=len(classes),
                     representatives=[(r['id'],r['maximal_independent_count']) for r in representatives])))
