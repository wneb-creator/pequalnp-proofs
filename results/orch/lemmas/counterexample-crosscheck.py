from itertools import combinations
import time


def crosscheck(p, l, depth):
    n = p + l
    assignments = range(1 << n)
    targets = {}
    for edge_mask in range(1, 1 << (p * l)):
        edges = [(a, p + b) for a in range(p) for b in range(l) if edge_mask >> (a * l + b) & 1]
        if any(all((a, b) in edges for a in pair_a for b in pair_b)
               for pair_a in combinations(range(p), 2) for pair_b in combinations(range(p, n), 2)):
            continue
        cover = min(s.bit_count() for s in assignments
                    if all((s >> a & 1) or (s >> b & 1) for a, b in edges))
        truth = frozenset(x for x in assignments if any(x >> a & 1 and x >> b & 1 for a, b in edges))
        targets[truth] = (edge_mask, len(edges) + cover - 1)
    values = [frozenset(x for x in assignments if x >> i & 1) for i in range(n)]
    reach = [frozenset([i]) for i in range(n)]
    found = {}
    counts = [0] * (depth + 1)

    def visit(d):
        counts[d] += 1
        if d == depth:
            return
        for a in range(n + d):
            for b in range(a, n + d):
                for operation in ['and', 'or']:
                    r = reach[a] | reach[b] if operation == 'or' else frozenset()
                    if any(i < p for i in r) and any(i >= p for i in r):
                        continue
                    v = values[a] | values[b] if operation == 'or' else values[a] & values[b]
                    if v in targets:
                        edge_mask, bound = targets[v]
                        if d + 1 < bound:
                            raise AssertionError((edge_mask, bound, d + 1))
                        found[edge_mask] = min(d + 1, found.get(edge_mask, depth + 1))
                    values.append(v)
                    reach.append(r)
                    visit(d + 1)
                    reach.pop()
                    values.pop()

    started = time.monotonic()
    visit(0)
    print('Split', p, l, 'depth', depth, 'targets', len(targets), 'raw counts', counts)
    print('Observed minima', sorted(found.items()))
    print('No counterexample; elapsed seconds', time.monotonic() - started)
    if depth >= max(bound for _, bound in targets.values()):
        assert len(found) == len(targets)
        assert all(found[mask] == bound for mask, bound in targets.values())
        print('All minima equal the asserted bound.')


if __name__ == '__main__':
    crosscheck(2, 2, 4)
