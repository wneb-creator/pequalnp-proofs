"""Finite membership-type audit for products of three linear OR clauses.

Each variable has a nonzero 3-bit clause membership. Pattern111 would itself
satisfy all clauses, and is excluded for a homogeneous degree-two function.
Multiplicity is capped at2 because a C4 or repeated-center obstruction needs
at most two copies of any membership type. This is evidence and an explicit
case-analysis aid, not a machine-checked Lean theorem.
"""
from itertools import product, combinations
from pathlib import Path
import json


def evaluate(types):
    edges = [(i, j) for i, j in combinations(range(len(types)), 2)
             if types[i] | types[j] == 7]
    adjacency = [{j for a, j in edges if a == i} | {a for a, j in edges if j == i}
                 for i in range(len(types))]
    # An unused variable does not participate in the homogeneous graph function.
    if not edges or any(not a for a in adjacency):
        return None
    # Three clauses have hitting sets of size at most3, so this is exactly
    # the absence of prime implicants larger than2.
    for a, b, c in combinations(range(len(types)), 3):
        if types[a] | types[b] | types[c] == 7:
            if all(types[u] | types[v] != 7 for u, v in ((a, b), (a, c), (b, c))):
                return None
    # No odd triangle and no4cycle. For this membership-pattern graph,
    # the explicit BFS bipartiteness check also excludes longer oddcycles.
    color = {}
    for start in range(len(types)):
        if start in color:
            continue
        color[start] = 0
        stack = [start]
        while stack:
            a = stack.pop()
            for b in adjacency[a]:
                if b in color:
                    if color[b] == color[a]:
                        return None
                else:
                    color[b] = 1-color[a]
                    stack.append(b)
    if any(len(adjacency[a] & adjacency[b]) > 1
           for a, b in combinations(range(len(types)), 2)):
        return None
    centers = [i for i, a in enumerate(adjacency) if len(a) > 1]
    assert len(centers) <= 2
    if len(centers) == 2:
        assert centers[1] in adjacency[centers[0]]
    assert len(edges) == len(types)-1
    return {'types': types, 'edges': edges, 'centers': centers,
            'kind': 'double_star' if len(centers) == 2 else 'star'}


if __name__ == '__main__':
    results = []
    for counts in product(range(3), repeat=6):
        types = [p for p, count in enumerate(counts, 1) for _ in range(count)]
        result = evaluate(types)
        if result:
            result['counts'] = counts
            results.append(result)
    data = {'multiplicity_vectors_checked': 3**6,
            'surviving': len(results),
            'star_cases': sum(r['kind'] == 'star' for r in results),
            'double_star_cases': sum(r['kind'] == 'double_star' for r in results),
            'cases': results}
    output = Path('/tmp/oec/pequalnp-pilot-110/counterexample2583/three-clause-blocks.json')
    output.write_text(json.dumps(data, indent=2))
    print(json.dumps({k: v for k, v in data.items() if k != 'cases'}))
