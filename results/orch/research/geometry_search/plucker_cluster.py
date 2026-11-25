import itertools
import json
from pathlib import Path
import random
import time
import numpy as np

p = 5
planes = json.loads(Path('/tmp/oec/pequalnp-pilot-78/finitefield/f5-2planes.json').read_text())
pairs = list(itertools.combinations(range(10), 2))
V = np.array([[((a[i]*b[j]-a[j]*b[i]) % p) for i,j in pairs] for a,b in planes], dtype=np.int64)
for row in V:
    k = next(i for i,x in enumerate(row) if x)
    row[:] = row * pow(int(row[k]), -1, p) % p

def rref(rows):
    rows = rows.copy()
    pivots = []
    rank = 0
    for j in range(rows.shape[1]):
        choices = np.flatnonzero(rows[rank:,j])
        if not len(choices):
            continue
        k = rank + int(choices[0])
        rows[[rank,k]] = rows[[k,rank]]
        rows[rank] = rows[rank] * pow(int(rows[rank,j]), -1, p) % p
        for i in range(rows.shape[0]):
            if i != rank:
                rows[i] = (rows[i] - rows[i,j]*rows[rank]) % p
        pivots.append(j)
        rank += 1
        if rank == rows.shape[0]:
            break
    return rows[:rank], pivots

counts = {}
clusters = {}
rng = random.Random(231)
best = 0
t0 = time.monotonic()
for it in range(10000):
    selection = rng.sample(range(len(V)),4)
    R, pivots = rref(V[selection])
    if len(pivots) != 4:
        continue
    W = V.copy()
    for row,j in zip(R,pivots):
        W = (W - W[:,j,None]*row) % p
    members = tuple(map(int,np.flatnonzero(~np.any(W,axis=1))))
    count = len(members)
    counts[count] = counts.get(count,0)+1
    if count >= 8:
        clusters[members] = R.tolist()
    if count > best:
        best = count
        print('BEST',it,count,members,flush=True)
print('HISTOGRAM',counts,'SECONDS',time.monotonic()-t0,flush=True)
out = [{'members':list(m),'span':r} for m,r in clusters.items()]
Path('/tmp/oec/pequalnp-pilot-78/geometry_search/plucker-clusters.json').write_text(json.dumps(out))
print('CLUSTERS',len(out),flush=True)
