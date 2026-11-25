from itertools import combinations
from pathlib import Path
import json

EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
         (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
ALL = (1 << len(EDGES))-1


def covered(vertices):
    return sum(1 << j for j, (a,b) in enumerate(EDGES)
               if vertices >> a & 1 or vertices >> b & 1)


def main():
    minimum = [11] * (ALL+1)
    for vertices in range(1 << 10):
        mask = covered(vertices)
        minimum[mask] = min(minimum[mask], vertices.bit_count())
    for bit in range(15):
        for mask in range(ALL+1):
            if not mask >> bit & 1:
                minimum[mask] = min(minimum[mask], minimum[mask | (1 << bit)])
    assert minimum[ALL] == 6
    assert all(minimum[ALL ^ (1 << j)] == 6 for j in range(15))
    distributions = {}
    cases = []
    for count in range(4):
        distribution = {}
        for missing in combinations(range(15), count):
            clean = ALL ^ sum(1 << j for j in missing)
            cover = minimum[clean]
            distribution[cover] = distribution.get(cover,0)+1
            cases.append({'missing_indices':missing, 'missing_edges':[EDGES[j] for j in missing],
                          'clean_edges':15-count, 'minimum_cover':cover,
                          'counted_gate_slack_at_size19':20-(15-count)-cover})
        distributions[count] = distribution
    five_vertex_induced = {}
    for vertices in combinations(range(10),5):
        s=set(vertices)
        count=sum(a in s and b in s for a,b in EDGES)
        five_vertex_induced[count]=five_vertex_induced.get(count,0)+1
    result={'graph_edges':EDGES,'cover_distributions_by_missing_edges':distributions,
            'five_vertex_induced_edge_counts':five_vertex_induced,'cases':cases,
            'scope':'Finite cover combinatorics only; no circuit lower bound without additional counting hypotheses.'}
    root=Path('results/orch2590/lemmas/counterexample')
    (root/'cover-profiles.json').write_text(json.dumps(result,indent=2))
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','graph_edges')}))


if __name__ == '__main__':
    main()
