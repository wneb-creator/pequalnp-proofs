import itertools
import json
from collections import Counter
from pathlib import Path


def partitions(length):
    def go(xs, largest):
        if len(xs) == length:
            yield tuple(xs)
            return
        for x in range(largest + 2):
            yield from go(xs + [x], max(largest, x))
    yield from go([0], 0)


group_orders = []
for swap_root in [False, True]:
    for swap_left, swap_right in itertools.product([False, True], repeat=2):
        left = [1, 0] if swap_left else [0, 1]
        right = [3, 2] if swap_right else [2, 3]
        group_orders.append(right + left if swap_root else left + right)


def canonical(xs):
    best = None
    for order in group_orders:
        for flips in itertools.product([False, True], repeat=4):
            ys = []
            for i, flip in zip(order, flips):
                ys += list(reversed(xs[2*i:2*i+2])) if flip else list(xs[2*i:2*i+2])
            labels = {}
            z = tuple(labels.setdefault(y, len(labels)) for y in ys)
            if best is None or z < best:
                best = z
    return best


def minterms(factors):
    terms = {frozenset(t) for t in itertools.product(*factors)}
    return sorted((t for t in terms if not any(s < t for s in terms)),
                  key=lambda t: (len(t), sorted(t)))


def contains_edge(term, edges):
    return any(u in term and v in term for u, v in edges)


def add_allowed(n, edges, edge):
    u, v = edge
    nbr = [set() for _ in range(n)]
    for a, b in edges:
        nbr[a].add(b)
        nbr[b].add(a)
    if nbr[u] & nbr[v]:
        return False
    return not any(b in nbr[a] for a in nbr[u] for b in nbr[v])


def safe_graph(n, terms, left, right, hybrid_edges):
    mandatory = {tuple(sorted(t)) for t in terms if len(t) == 2} | set(hybrid_edges)
    edges = set()
    for edge in sorted(mandatory):
        if not add_allowed(n, edges, edge):
            return None
        edges.add(edge)
    explored = set()

    def search(es):
        key = frozenset(es)
        if key in explored:
            return None
        explored.add(key)
        missing = [t for t in terms if not contains_edge(t, es)]
        if not missing:
            if all(contains_edge(t, es) for t in left):
                return None
            if all(contains_edge(t, es) for t in right):
                return None
            return sorted(es)
        choices = []
        for term in missing:
            available = [edge for edge in itertools.combinations(sorted(term), 2)
                         if add_allowed(n, es, edge)]
            if not available:
                return None
            choices.append(available)
        for edge in min(choices, key=len):
            found = search(es | {edge})
            if found is not None:
                return found
        return None

    return search(edges)


patterns = set()
counts = Counter()
results = []
for xs in partitions(8):
    if max(xs) + 1 > 6 or any(xs[i] == xs[i+1] for i in range(0, 8, 2)):
        continue
    key = canonical(xs)
    if key in patterns:
        continue
    patterns.add(key)
    factors = [tuple(key[2*i:2*i+2]) for i in range(4)]
    if set(factors[0]) == set(factors[1]) or set(factors[2]) == set(factors[3]):
        continue
    left, right = minterms(factors[:2]), minterms(factors[2:])
    terms = minterms(factors)
    if any(len(t) == 1 for t in terms):
        continue
    pairs = [sorted(t) for t in terms if len(t) == 2]
    if len(pairs) < 2 or left == terms or right == terms or left == right:
        continue
    counts['eligible_patterns'] += 1
    n = max(key) + 1
    hybrid_edges = []
    for i in [0, 2]:
        p, q = set(factors[i]), set(factors[i+1])
        if len(p & q) == 1:
            hybrid_edges.append(tuple(sorted(p ^ q)))
    graph = safe_graph(n, terms, left, right, hybrid_edges)
    if graph is None:
        counts['no_safe_girth_graph'] += 1
        continue
    counts['safe_patterns'] += 1
    counts['vertices_' + str(n)] += 1
    results.append({'n': n, 'factors': factors, 'pairs': pairs,
                    'mandatory_hybrid_edges': hybrid_edges,
                    'minterms': [sorted(t) for t in terms],
                    'graph': graph})

report = {'counts': dict(counts), 'results': results}
Path('/tmp/oec/pequalnp-pilot-77/literal-clusters.json').write_text(json.dumps(report, indent=2))
print(json.dumps(report, indent=2))
