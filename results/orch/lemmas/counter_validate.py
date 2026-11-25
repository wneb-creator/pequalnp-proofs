"""Finite plane checks; exploration, not a Lean certificate."""
from collections import Counter
from pathlib import Path
import hashlib
import json
from itertools import permutations


def plane(q, offsets):
    n = q*q+q+1
    lines = [{(i+d) % n for d in offsets} for i in range(n)]
    assert all(len(line) == q+1 for line in lines)
    assert all(sum(p in line and r in line for line in lines) == 1
               for p in range(n) for r in range(p))
    edges = [(p, n+l) for l, line in enumerate(lines) for p in sorted(line)]
    masks = [sum(1 << p for p in line) for line in lines]
    false_maximal = []
    for x in range(1 << n):
        ys = [l for l, mask in enumerate(masks) if not x & mask]
        covered = 0
        for l in ys:
            covered |= masks[l]
        if x | covered == (1 << n)-1:
            false_maximal.append(x | sum(1 << (n+l) for l in ys))
    circuit = []
    stars = []
    def gate(op, a, b):
        circuit.append((op,a,b))
        return 2*n+len(circuit)-1
    for l, points in enumerate(lines):
        points = sorted(points)
        root = points[0]
        for p in points[1:]:
            root = gate('or',root,p)
        stars.append(gate('and',root,n+l))
    root = stars[0]
    for star in stars[1:]:
        root = gate('or',root,star)
    def evaluate(mask):
        values = [bool(mask & 1 << i) for i in range(2*n)]
        for op,a,b in circuit:
            values.append(values[a] and values[b] if op == 'and' else values[a] or values[b])
        return values[-1]
    minimal_true = [(1 << p) | (1 << l) for p,l in edges]
    assert all(evaluate(mask) for mask in minimal_true)
    assert all(not evaluate(mask) for mask in false_maximal)
    assert len(circuit) == n*(q+2)-1
    if q == 2:
        for mask in range(1 << (2*n)):
            want = any(mask & (1 << p) and mask & (1 << l) for p,l in edges)
            assert evaluate(mask) == want
            if not want:
                assert any(mask & ~f == 0 for f in false_maximal)
            else:
                assert any(t & ~mask == 0 for t in minimal_true)
    return dict(q=q, n=n, offsets=offsets, points_per_line=q+1,
                lines_per_point=sorted(set(sum(p in line for line in lines) for p in range(n))),
                edges=len(edges), maximal_false=len(false_maximal),
                critical_count=len(edges)+len(false_maximal),
                false_size_counts=dict(sorted(Counter(x.bit_count() for x in false_maximal).items())),
                standard_star_gate_count=len(circuit),
                full_truth_table_verified=(q == 2))


if __name__ == '__main__':
    rows = [plane(2,[0,1,3]), plane(3,[0,1,3,9])]
    n=7
    lines=[frozenset((l+d)%n for d in [0,1,3]) for l in range(n)]
    lookup={points:l for l,points in enumerate(lines)}
    autos=[]
    for perm in permutations(range(n)):
        images=[frozenset(perm[x] for x in line) for line in lines]
        if all(points in lookup for points in images):
            autos.append(tuple(perm)+tuple(n+lookup[points] for points in images))
    dual=tuple(n+(-p)%n for p in range(n))+tuple((-l)%n for l in range(n))
    full=autos+[tuple(dual[a[i]] for i in range(2*n)) for a in autos]
    edges={tuple(sorted((p,n+l))) for l,line in enumerate(lines) for p in line}
    assert all({tuple(sorted((a[x],a[y]))) for x,y in edges}==edges for a in full)
    reps=[(0,1),(0,7),(0,8)]
    orbits=[{tuple(sorted((a[x],a[y]))) for a in full} for x,y in reps]
    assert len(set.union(*orbits))==91
    assert sum(map(len,orbits))==91
    symmetry=dict(color_preserving_automorphisms=len(autos),full_automorphisms=len(full),
                  representatives=reps,orbit_sizes=list(map(len,orbits)),all_distinct_input_pairs_covered=True)
    print(json.dumps(dict(rows=rows, symmetry=symmetry,
                         source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),indent=2))
