"""Search a two-dirty-products effective-mask cover conjecture on five small hosts."""
import argparse
import itertools
import json
import time
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--incomparable', action='store_true')
    parser.add_argument('--disjoint-min-two', action='store_true')
    parser.add_argument('--private-joint', action='store_true')
    parser.add_argument('--edge-budget', action='store_true')
    parser.add_argument('--vertices', type=int, choices=(6,8), default=6)
    parser.add_argument('--seconds', type=float, default=60)
    args = parser.parse_args()
    started = time.monotonic()
    n = args.vertices
    inputs = [sum(1 << assignment for assignment in range(1 << n)
                  if assignment >> i & 1) for i in range(n)]
    sums = [0] * (1 << n)
    for selected in range(1, 1 << n):
        low = selected & -selected
        sums[selected] = sums[selected-low] | inputs[low.bit_length()-1]
    functions = {}
    for a in range(1, 1 << n):
        for b in range(a, 1 << n):
            if args.disjoint_min_two and (a & b or min(a.bit_count(),b.bit_count()) < 2):
                continue
            if args.incomparable and (a & b in (a, b)):
                continue
            functions.setdefault(sums[a] & sums[b], (a, b))
    hosts = [
        ('cycle6', [(0,3),(0,4),(1,4),(1,5),(2,5),(2,3)]),
        ('path6', [(0,3),(1,3),(1,4),(2,4),(2,5)]),
        ('tree122', [(0,3),(0,4),(0,5),(1,4),(2,5)]),
        ('path4_edge', [(0,3),(1,3),(1,4),(2,5)]),
        ('matching3', [(0,3),(1,4),(2,5)])]
    if n == 8:
        hosts = [
            ('cycle8',[(0,4),(0,5),(1,5),(1,6),(2,6),(2,7),(3,7),(3,4)]),
            ('path8',[(0,4),(0,5),(1,5),(1,6),(2,6),(2,7),(3,7)]),
            ('cover4_example',[(0,4),(0,5),(0,6),(1,4),(2,5),(2,7),(3,5),(1,7)]),
            ('overlap_budget_example',[(0,3),(0,4),(0,5),(0,6),(1,3),(2,3),(1,7)]),
            ('matching4',[(0,4),(1,5),(2,6),(3,7)])]
    print(json.dumps({'unique_product_functions': len(functions),
                      'incomparable_operands': args.incomparable,
                      'disjoint_min_two': args.disjoint_min_two,
                      'private_joint_required': args.private_joint,
                      'test_edge_budget': args.edge_budget}), flush=True)
    summaries = []
    best = {}
    for name, edges in hosts:
        target = 0
        for a, b in edges:
            target |= inputs[a] & inputs[b]
        edge_assignments = [(1 << a) | (1 << b) for a, b in edges]
        incidents = [sum(1 << j for j, edge in enumerate(edges) if vertex in edge)
                     for vertex in range(n)]
        bad_cover = []
        for selected in range(1 << len(edges)):
            bad_cover.append(not any(selected & ~(incidents[a] | incidents[b]) == 0
                                     for a, b in itertools.combinations(range(n), 2)))
        vertex_covers=[]
        for vertices in range(1<<n):
            covered=0
            for u in range(n):
                if vertices>>u&1:covered|=incidents[u]
            vertex_covers.append((vertices.bit_count(),covered))
        cover_cache={}
        candidates = []
        for truth, (a, b) in functions.items():
            bad = truth & ~target
            if not bad:
                continue
            accepted = sum(1 << j for j, assignment in enumerate(edge_assignments)
                           if truth >> assignment & 1)
            effective = [i for i in range(n) if not (bad & inputs[i])]
            union = 0
            for i in effective:
                union |= accepted & incidents[i]
            candidates.append((truth, bad, accepted, union, effective, a, b))
        checked = productive = 0
        for i, first in enumerate(candidates):
            if time.monotonic()-started >= args.seconds:
                partial={'host':name,'outer_index':i,'dirty_products':len(candidates),
                         'product_pairs_checked':checked,'productive_joint_clean_pairs':productive}
                args.output.write_text(json.dumps({'counterexample':None,'timeout':partial,'completed_hosts':summaries},indent=2)+'\n')
                print('TIMEOUT '+json.dumps(partial),flush=True)
                return
            for second in candidates[i+1:]:
                checked += 1
                if first[1] & second[1]:
                    continue
                joint = first[2] & second[2]
                if not joint:
                    continue
                productive += 1
                union = joint | first[3] | second[3]
                if args.private_joint and not (joint & ~(first[3] | second[3])):
                    continue
                sets=[first[5],first[6],second[5],second[6]]
                or_cost=sum(s.bit_count()-1 for s in sets)
                if args.disjoint_min_two:
                    # Shared intersections are disjoint quadrants; build each once.
                    or_cost-=sum(max((a&b).bit_count()-1,0) for a in sets[:2] for b in sets[2:])
                if union not in cover_cache:
                    cover_cache[union]=min(size for size,covered in vertex_covers if union&~covered==0)
                cover=cover_cache[union]
                score=cover
                category=str(bool(first[3]) and bool(second[3]))
                violates=category not in best or score>best[category]['score']
                if violates:
                    result = {'host': name, 'edges': edges,
                              'A': [j for j in range(n) if first[5] >> j & 1],
                              'B': [j for j in range(n) if first[6] >> j & 1],
                              'C': [j for j in range(n) if second[5] >> j & 1],
                              'D': [j for j in range(n) if second[6] >> j & 1],
                              'effective_first': first[4], 'effective_second': second[4],
                              'joint_edges': [edge for j, edge in enumerate(edges) if joint >> j & 1],
                              'union_edges': [edge for j, edge in enumerate(edges) if union >> j & 1],
                              'incomparable_operands': args.incomparable,
                              'private_joint_required':args.private_joint,
                              'disjoint_min_two':args.disjoint_min_two,
                              'known_or_dag_cost':or_cost,'union_cover':cover,'score':score,'both_mask_unions_nonempty':category=='True'}
                    best[category]=result
                    print('NEW_BEST '+json.dumps(result),flush=True)
        summary = {'host': name, 'dirty_products': len(candidates),
                   'product_pairs_checked': checked, 'productive_joint_clean_pairs': productive,
                   'counterexample_found': False}
        summaries.append(summary)
        print(json.dumps(summary), flush=True)
    args.output.write_text(json.dumps({'best_by_both_masks':best,'completed_hosts':summaries},indent=2)+'\n')


if __name__ == '__main__':
    main()
