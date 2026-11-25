from collections import Counter
from functools import lru_cache

edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
adj=[0]*10
for u,v in edges:adj[u]|=1<<v;adj[v]|=1<<u
full=(1<<10)-1

def close(deleted):
    return deleted | sum(1<<v for v in range(10) if adj[v] & ~deleted == 0)

def moves(deleted):
    classes={}
    for v in range(10):
        if not deleted>>v&1:
            row=adj[v]&~deleted
            if row:classes[row]=classes.get(row,0)|(1<<v)
    return sorted((close(deleted|group),group,row) for row,group in classes.items())

@lru_cache(None)
def routes(deleted,steps):
    if deleted==full:return ((),) if steps==0 else ()
    if steps==0:return ()
    return tuple(((group,row),)+tail for nxt,group,row in moves(deleted) for tail in routes(nxt,steps-1))

rs=routes(close(0),6)
print('six-step maximal-twin elimination paths',len(rs))
shape=Counter(tuple(g.bit_count() for g,r in path) for path in rs)
print('class-size shapes',sorted(shape.items()))
print('remaining-neighbor-degree shapes',Counter(tuple(r.bit_count() for g,r in path) for path in rs))
print('removed class-total',Counter(sum(g.bit_count() for g,r in path) for path in rs))
print('example paths per shape')
for sh in sorted(shape):
    path=next(p for p in rs if tuple(g.bit_count() for g,r in p)==sh)
    print(sh,[([v for v in range(10) if g>>v&1],[v for v in range(10) if r>>v&1]) for g,r in path])
