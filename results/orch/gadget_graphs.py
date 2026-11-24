import itertools
import json
import sys

from rectangle_search import c4free, edge, mincover


source = json.load(open(sys.argv[1]))
n = source['n']
old = {edge(u,v) for u,v in source['edges']}
repair_sets = [{edge(5,8)}]
repair_sets.extend({edge(z,c) for z,c in zip([0,1,3,6],centers)}
                   for centers in itertools.product([5,8],repeat=4))
records = []
for added in repair_sets:
    cases = []
    for k in range(8):
        for deleted in itertools.combinations(old,k):
            graph = (old-set(deleted)) | added
            if c4free(n,graph):
                cover = mincover(n,graph)
                cases.append(dict(deleted=sorted(deleted),edges=len(graph),
                                  tau=cover.bit_count(),cover=cover,
                                  bound=len(graph)+cover.bit_count()-1))
        if cases:
            break
    records.append(dict(added=sorted(added),minimum_deletions=k if cases else None,
                        feasible_count=len(cases),
                        best=max(cases,key=lambda r:r['bound']) if cases else None,
                        maximum_bound=max((r['bound'] for r in cases),default=None)))
print(json.dumps(records,indent=2))
