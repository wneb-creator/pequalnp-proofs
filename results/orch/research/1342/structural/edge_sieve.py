import itertools
import json
from collections import Counter
from pathlib import Path

EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
edge_masks = [(1 << a) | (1 << b) for a,b in EDGES]
covers = sorted(range(1 << 11), key=int.bit_count)

def minimum_cover(indices):
    for mask in covers:
        if all(mask & edge_masks[i] for i in indices):
            return mask.bit_count()

assert minimum_cover(range(16)) == 7
report = {"edges": EDGES, "cover_number": 7, "sizes": {}}
for u in range(5):
    counts = Counter()
    tight = []
    for removed in itertools.combinations(range(16), u):
        rem = set(removed)
        tau = minimum_cover([i for i in range(16) if i not in rem])
        counts[tau] += 1
        if u == 2 and tau == 5:
            a,b = removed
            tight.append({"removed_indices": removed, "removed_edges": [EDGES[a],EDGES[b]],
                          "disjoint": not bool(edge_masks[a] & edge_masks[b])})
    report["sizes"][u] = {"remaining_cover_histogram": dict(sorted(counts.items())),
                          "two_edge_tight_cases": tight}

out=Path(__file__).with_name('edge-sieve.json')
out.write_text(json.dumps(report, indent=2)+'\n')
for u, row in report['sizes'].items():
    print('removed',u,'cover_histogram',row['remaining_cover_histogram'])
print('u=2, remaining cover 5:',len(report['sizes'][2]['two_edge_tight_cases']))
print('all disjoint:',all(row['disjoint'] for row in report['sizes'][2]['two_edge_tight_cases']))
