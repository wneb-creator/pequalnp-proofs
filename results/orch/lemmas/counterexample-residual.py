from itertools import combinations
import json
import time


def test_residual(n, edges, target, values, gates):
    reach = [frozenset([i]) for i in range(n)]
    closure = [frozenset() for _ in range(n)]
    ancestor = [frozenset() for _ in range(n)]
    clean_and = {j for j, (op, _, _) in enumerate(gates) if op == 'and' and values[n + j] <= target}
    for j, (op, a, b) in enumerate(gates):
        if op == 'and' and clean_and & (ancestor[a] | ancestor[b]):
            return None
        reach.append(reach[a] | reach[b] if op == 'or' else frozenset())
        closure.append(frozenset([j]) | (closure[a] | closure[b] if op == 'or' else frozenset()))
        ancestor.append(frozenset([j]) | ancestor[a] | ancestor[b])
    stars = set()
    centres_empty = set()
    for j in clean_and:
        _, a, b = gates[j]
        if not reach[a] or not reach[b]:
            centres_empty.add(j)
        stars.update(tuple(sorted([u, v])) for u in reach[a] for v in reach[b])
    residual = set(edges) - stars
    tau = min(s.bit_count() for s in range(1 << n)
              if all(s >> a & 1 or s >> b & 1 for a, b in residual))
    dirty_and = {j for j, (op, _, _) in enumerate(gates) if op == 'and' and not values[n + j] <= target}
    dirty_or = {j for j, (op, _, _) in enumerate(gates) if op == 'or' and not values[n + j] <= target}
    lam = set()
    for h in dirty_or:
        _, a, b = gates[h]
        if not reach[a] or not reach[b]:
            continue
        for j in clean_and:
            _, u, v = gates[j]
            if (len(reach[v]) == 1 and h in closure[u]) or (len(reach[u]) == 1 and h in closure[v]):
                lam.add(h)
    c, j, o, U = len(centres_empty), len(dirty_and), len(dirty_or - lam), len(residual)
    checks = [U + tau <= 2 * c + j + o, U <= c + o, tau <= c + j]
    if not all(checks):
        print('RESIDUAL FAILURE', json.dumps({'n': n, 'edges': edges, 'gates': gates,
              'U': sorted(residual), 'tau_U': tau, 'c': c, 'j': j, 'o': o, 'checks': checks}), flush=True)
        raise SystemExit(1)
    return U, tau, c, j, o


def search(p=2, l=2, depth=4):
    n = p + l
    targets = {}
    for mask in range(1, 1 << (p * l)):
        edges = [(a, p + b) for a in range(p) for b in range(l) if mask >> (a * l + b) & 1]
        if any(all((a, b) in edges for a in aa for b in bb)
               for aa in combinations(range(p), 2) for bb in combinations(range(p, n), 2)):
            continue
        tau = min(s.bit_count() for s in range(1 << n)
                  if all(s >> a & 1 or s >> b & 1 for a, b in edges))
        truth = frozenset(x for x in range(1 << n) if any(x >> a & 1 and x >> b & 1 for a, b in edges))
        targets[truth] = edges, len(edges) + tau - 1
    values = [frozenset(x for x in range(1 << n) if x >> i & 1) for i in range(n)]
    reach = [frozenset([i]) for i in range(n)]
    gates = []
    checked = 0
    summaries = set()
    optimal = 0

    def visit(d):
        nonlocal checked, optimal
        if d == depth:
            return
        for a in range(n + d):
            for b in range(a, n + d):
                for op in ['and', 'or']:
                    r = reach[a] | reach[b] if op == 'or' else frozenset()
                    if any(i < p for i in r) and any(i >= p for i in r):
                        continue
                    v = values[a] | values[b] if op == 'or' else values[a] & values[b]
                    values.append(v)
                    reach.append(r)
                    gates.append((op, a, b))
                    if v in targets and targets[v][1] == d + 1:
                        optimal += 1
                        result = test_residual(n, targets[v][0], v, values, gates)
                        if result is not None:
                            checked += 1
                            summaries.add(result)
                    visit(d + 1)
                    gates.pop()
                    reach.pop()
                    values.pop()

    started = time.monotonic()
    visit(0)
    print('Optimal circuits', optimal, 'TopForm circuits checked', checked)
    print('Observed (U,tau_U,c,j,o)', sorted(summaries))
    print('All three residual inequalities passed; elapsed seconds', time.monotonic() - started)


if __name__ == '__main__':
    search()
