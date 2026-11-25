"""Independent graph orbit and biclique-cover audit for the six-vertex search."""
import itertools
import json
from functools import lru_cache
from pathlib import Path

ROOT = Path('/tmp/oec/pequalnp-pilot-82')
records = json.loads((ROOT / 'finite-search/graphs6.json').read_text())
edges = list(itertools.combinations(range(6), 2))
edge_index = {e:i for i,e in enumerate(edges)}
universe = {}
for record in records:
    g = record['graph']
    edge_list = [e for i,e in enumerate(edges) if (g >> i) & 1]
    for permutation in itertools.permutations(range(6)):
        renamed = sum(1 << edge_index[tuple(sorted((permutation[a],permutation[b])))]
                      for a,b in edge_list)
        if renamed in universe:
            assert universe[renamed] == g, (renamed,universe[renamed],g)
        universe[renamed] = g
assert len(universe) == 32768
assert set(universe) == set(range(32768))
print('ORBIT COVERAGE: exactly 156 disjoint orbits cover all 32768 labeled graphs.',flush=True)

for record in records:
    graph = record['graph']
    neighbor = [0] * 6
    for i,(a,b) in enumerate(edges):
        if graph >> i & 1:
            neighbor[a] |= 1 << b
            neighbor[b] |= 1 << a
    # Every biclique may be enlarged on its right side to the full common
    # neighborhood of its nonempty left side, so these suffice for exact cover.
    bicliques = set()
    for left in range(1,64):
        right = 63
        for a in range(6):
            if left >> a & 1:
                right &= neighbor[a]
        covered = 0
        for i,(a,b) in enumerate(edges):
            if (left >> a & 1 and right >> b & 1) or (left >> b & 1 and right >> a & 1):
                covered |= 1 << i
        if covered:
            assert covered & ~graph == 0
            bicliques.add(covered)
    covering = {1 << e: [b for b in bicliques if b >> e & 1] for e in range(15)}
    @lru_cache(None)
    def minimum(uncovered):
        if uncovered == 0:
            return 0
        first = uncovered & -uncovered
        return 1 + min(minimum(uncovered & ~b) for b in covering[first])
    actual = minimum(graph)
    assert actual == record['biclique_cover'], (graph,actual,record['biclique_cover'])
    print('COVER',graph,actual,flush=True)
print('BICLIQUE AUDIT: all 156 supplied cover numbers independently confirmed.',flush=True)
