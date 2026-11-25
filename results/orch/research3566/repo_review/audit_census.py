"""Independent, bounded review of the candidate graph data (no solver calls).

Usage: python3 audit_census.py PROOF_ROUTE_DIR OUTPUT_JSON
The original census scripts and files are only read, never imported or modified.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time

source = Path(sys.argv[1])
output = Path(sys.argv[2])
started = time.monotonic()

def canonical(rows, width):
    variants = [rows]
    if len(rows) == width:
        variants.append([sum(1 << a for a, r in enumerate(rows) if r >> b & 1)
                         for b in range(width)])
    best = None
    for perm in itertools.permutations(range(width)):
        for rs in variants:
            key = tuple(sorted(sum(1 << perm[b] for b in range(width) if r >> b & 1)
                               for r in rs))
            if best is None or key < best:
                best = key
    return best

def inspect(spec, left):
    n = spec['n']
    edges = [tuple(e) for e in spec['edges']]
    assert len(set(edges)) == len(edges)
    assert all(0 <= a < left <= b < n for a, b in edges)
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    common = max(len(adj[a] & adj[b]) for a in range(n) for b in range(a))
    assert common <= 1
    # Matching lower bound and explicit left-side cover give tau=left.
    right_match = {}
    def augment(a, seen):
        for b in sorted(adj[a]):
            if b in seen:
                continue
            seen.add(b)
            if b not in right_match or augment(right_match[b], seen):
                right_match[b] = a
                return True
        return False
    for a in range(left):
        augment(a, set())
    matching = sorted((a, b) for b, a in right_match.items())
    assert len(matching) == left
    independent = []
    max_negative = []
    minimum_cover = n
    for x in range(1 << n):
        if not any(x >> a & 1 and x >> b & 1 for a, b in edges):
            independent.append(x)
            minimum_cover = min(minimum_cover, n - x.bit_count())
            if all(x >> j & 1 or any(x >> u & 1 for u in adj[j]) for j in range(n)):
                max_negative.append(x)
    assert minimum_cover == left
    if 'matching' in spec:
        mm = [tuple(e) for e in spec['matching']]
        assert len(mm) == left and len(set(itertools.chain.from_iterable(mm))) == 2 * left
        assert all(e in edges for e in mm)
    for key in ['tau', 'cover']:
        if key in spec:
            assert spec[key] == left
    expected = len(edges) + left - 1
    for key in ['expected_size', 'star_cover_upper']:
        if key in spec:
            assert spec[key] == expected
    if 'max_independent_sets' in spec:
        assert spec['max_independent_sets'] == len(max_negative)
    rows = [sum(1 << (b - left) for b in adj[a]) for a in range(left)]
    canon = canonical(rows, n - left)
    if 'canonical_rows' in spec:
        assert tuple(spec['canonical_rows']) == canon
    for side, actual in [('left_degrees', [len(adj[a]) for a in range(left)]),
                         ('right_degrees', [len(adj[b]) for b in range(left, n)])]:
        if side in spec:
            assert spec[side] == actual
    # Validate every reported fundamental cycle and its GF(2) independence.
    basis = {}
    for cyc in spec.get('cycle_basis', []):
        assert len(cyc) == len(set(cyc)) >= 6
        bits = 0
        for a, b in zip(cyc, cyc[1:] + cyc[:1]):
            edge = (min(a, b), max(a, b))
            assert edge in edges
            bits ^= 1 << edges.index(edge)
        while bits and bits.bit_length() in basis:
            bits ^= basis[bits.bit_length()]
        assert bits
        basis[bits.bit_length()] = bits
    unseen = set(range(n))
    components = 0
    while unseen:
        components += 1
        stack = [unseen.pop()]
        while stack:
            for b in adj[stack.pop()] & unseen:
                unseen.remove(b)
                stack.append(b)
    if 'cycle_basis' in spec:
        assert len(basis) == len(edges) - n + components
    return dict(name=spec['name'], n=n, edges=len(edges), left=left,
                tau=left, matching=matching, common_neighbor_max=common,
                minimum_degree=min(map(len, adj)), components=components,
                positive_rows=len(edges), maximal_negative_rows=len(max_negative),
                synthesis_rows=len(edges) + len(max_negative),
                expected_size=expected, refuting_size_at_most=expected - 1,
                rows=rows, canonical_rows=canon)

reports = {}
representatives = []
for filename, left in [('census5x5.json', 5), ('census6x6.json', 6),
                       ('census6x6m15.json', 6)]:
    report = json.loads((source / filename).read_text())
    reports[filename] = report
    for spec in report['classes']:
        representatives.append(inspect(spec, left))
representatives.append(inspect(json.loads((source / 'bip5x6_14.json').read_text()), 5))

# Recount the fixed-diagonal, minimum-degree-two 6x6 domains independently.
# Profiles are generated from all partitions instead of trusting source lists.
recounts = []
for edge_count, filename in [(16, 'census6x6.json'), (15, 'census6x6m15.json')]:
    profiles = [tuple(reversed(p)) for p in itertools.combinations_with_replacement(range(2, 7), 6)
                if sum(p) == edge_count and sum(math.comb(d, 2) for d in p) <= 15]
    counts = {}
    keys = set()
    for profile in profiles:
        accepted = [0]
        options = [[r for r in range(64) if r >> i & 1 and r.bit_count() == d]
                   for i, d in enumerate(profile)]
        def visit(rows):
            if len(rows) == 6:
                degrees = [sum(r >> j & 1 for r in rows) for j in range(6)]
                if min(degrees) < 2:
                    return
                accepted[0] += 1
                keys.add(canonical(rows, 6))
                return
            for r in options[len(rows)]:
                if all((r & s).bit_count() <= 1 for s in rows):
                    visit(rows + [r])
        visit([])
        counts[str(profile)] = accepted[0]
    original = reports[filename]
    assert sum(counts.values()) == original['accepted_profile_ordered']
    assert keys == {tuple(c['canonical_rows']) for c in original['classes']}
    assert set(profiles) == {tuple(p) for p in original['profiles']}
    recounts.append(dict(file=filename, scope='fixed perfect matching; both sides minimum degree at least 2',
                         profiles=profiles, profile_counts=counts, accepted=sum(counts.values()),
                         isomorphism_classes=len(keys)))

# A separate enumeration of 5x5: all 7 off-diagonal additions to a matching.
free = [(a, b) for a in range(5) for b in range(5) if a != b]
count = 0
keys = set()
for additions in itertools.combinations(free, 7):
    rows = [1 << a for a in range(5)]
    for a, b in additions:
        rows[a] |= 1 << b
    if all((rows[a] & rows[b]).bit_count() <= 1 for a in range(5) for b in range(a)):
        count += 1
        keys.add(canonical(rows, 5))
assert count == reports['census5x5.json']['accepted_labelled']
assert keys == {tuple(c['canonical_rows']) for c in reports['census5x5.json']['classes']}
recounts.append(dict(file='census5x5.json', scope='fixed perfect matching; no separate minimum-degree filter',
                     candidates=math.comb(20, 7), accepted=count, isomorphism_classes=len(keys)))

hashes = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
          for p in [source / 'census5x5.py', source / 'census6x6.py',
                    source / 'census6x6m15.py', source / 'census5x5.json',
                    source / 'census6x6.json', source / 'census6x6m15.json',
                    source / 'bip5x6_14.json']}
result = dict(verdict='PASS with the stated census scopes; computational diagnostics only',
              representatives=representatives, independent_recounts=recounts,
              source_sha256=hashes, elapsed_seconds=time.monotonic() - started)
output.write_text(json.dumps(result, indent=2) + '\n')
for r in representatives:
    print(f"{r['name']}: n={r['n']} m={r['edges']} tau={r['tau']} noC4=yes "
          f"rows={r['positive_rows']}+{r['maximal_negative_rows']}={r['synthesis_rows']} "
          f"expected={r['expected_size']} refutation<={r['refuting_size_at_most']}")
for r in recounts:
    print(f"{r['file']}: accepted={r['accepted']} classes={r['isomorphism_classes']} scope={r['scope']}")
print(f"PASS elapsed={result['elapsed_seconds']:.3f}s")
