import argparse
import json
from itertools import combinations
from pathlib import Path


class CNF:
    def __init__(self):
        self.n = 1
        self.clauses = [[1]]

    def var(self):
        self.n += 1
        return self.n

    def add(self, *xs):
        if 1 in xs:
            return
        ys = set(xs) - {-1}
        if any(-x in ys for x in ys):
            return
        self.clauses.append(sorted(ys, key=lambda x: (abs(x), x)))

    def and_(self, a, b):
        c = self.var()
        self.add(-a, -b, c)
        self.add(a, -c)
        self.add(b, -c)
        return c

    def or_(self, a, b):
        c = self.var()
        self.add(a, b, -c)
        self.add(-a, c)
        self.add(-b, c)
        return c

    def exactly_one(self, xs):
        self.add(*xs)
        for a, b in combinations(xs, 2):
            self.add(-a, -b)

    def equivalent_if(self, selector, a, b):
        self.add(-selector, -a, b)
        self.add(-selector, a, -b)

    def gate(self, op, a, b, z):
        self.add(-op, a, b, -z)
        self.add(-op, -a, z)
        self.add(-op, -b, z)
        self.add(op, -a, -b, z)
        self.add(op, a, -z)
        self.add(op, b, -z)

    def at_least(self, xs, k):
        if k <= 0:
            return
        prev = [1] + [-1] * k
        for x in xs:
            cur = [1]
            for j in range(1, k + 1):
                cur.append(self.or_(prev[j], self.and_(x, prev[j - 1])))
            prev = cur
        self.add(prev[k])

    def lower_thresholds(self, xs, k):
        # Only forward implications are needed when the resulting thresholds are upper bounded.
        prev = [1] + [-1] * k
        for x in xs:
            cur = [1]
            for j in range(1, k + 1):
                z = self.var()
                self.add(-prev[j], z)
                self.add(-x, -prev[j - 1], z)
                cur.append(z)
            prev = cur
        return prev


def generate(k, minimum, core, support, stem, violation=True, omitted=None, ordered=False, projected=False, patterns=False, fanout_budget=False, roots=2):
    n = 14
    assert 1 <= roots <= k
    root_indices = list(range(k - roots, k))
    edges = [(a, 7 + b) for a in range(7) for b in range(7)
             if (a - b) % 7 in (0, 1, 3)]
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    independent = []
    for m in range(1 << n):
        if any(m >> a & 1 and m >> b & 1 for a, b in edges):
            continue
        if all(m >> a & 1 or any(m >> b & 1 for b in adj[a]) for a in range(n)):
            independent.append(m)
    allowed = set(range(n)) if support is None else set(support)
    support_mask = sum(1 << a for a in allowed)
    if projected:
        projected_independent = {m & support_mask for m in independent}
        independent = sorted(m for m in projected_independent
            if not any(m != q and m & q == m for q in projected_independent))
    rows = independent + [(1 << a) | (1 << b) for a, b in edges] + [1 << a for a in range(n)]
    if projected:
        rows = [m & support_mask for m in rows]
    representatives = list(range(len(rows)))
    if projected:
        representatives = [rows.index(m) for m in dict.fromkeys(rows)]
    c = CNF()
    def row_vars():
        if not projected:
            return [c.var() for _ in rows]
        by_mask = {m: c.var() for m in dict.fromkeys(rows)}
        return [by_mask[m] for m in rows]
    def singleton_vars():
        return [c.var() if not projected or a in allowed else -1 for a in range(n)]
    def pair_vars():
        return [c.var() if not projected or a in allowed and b in allowed else -1 for a, b in edges]
    active_singletons = [a for a in range(n) if not projected or a in allowed]
    active_pairs = [e for e, (a, b) in enumerate(edges) if not projected or a in allowed and b in allowed]
    ops = [c.var() for _ in range(k)]
    selectors = [[[c.var() for _ in range(n + g)] for _ in range(2)] for g in range(k)]
    vals = [[1 if m >> i & 1 else -1 for m in rows] for i in range(n)]
    vals += [row_vars() for _ in range(k)]
    single = [[1 if a == i else -1 for a in range(n)] for i in range(n)]
    single += [singleton_vars() for _ in range(k)]
    pair = [[-1 for _ in edges] for _ in range(n)]
    pair += [pair_vars() for _ in range(k)]
    ports = []
    for g in range(k):
        for b in range(2):
            c.exactly_one(selectors[g][b])
            if support is not None:
                for a in range(n):
                    if a not in support:
                        c.add(-selectors[g][b][a])
        for a in range(n + g):
            for b in range(a):
                c.add(-selectors[g][0][a], -selectors[g][1][b])
        pv = [row_vars() for _ in range(2)]
        ps = [singleton_vars() for _ in range(2)]
        pp = [pair_vars() for _ in range(2)]
        ports.append(pv)
        for b in range(2):
            for a, sel in enumerate(selectors[g][b]):
                for r in representatives:
                    c.equivalent_if(sel, pv[b][r], vals[a][r])
                for u in active_singletons:
                    c.equivalent_if(sel, ps[b][u], single[a][u])
                for e in active_pairs:
                    c.equivalent_if(sel, pp[b][e], pair[a][e])
        for r in representatives:
            c.gate(ops[g], pv[0][r], pv[1][r], vals[n + g][r])
        for a in active_singletons:
            z = single[n + g][a]
            c.add(ops[g], -z)
            c.add(-ops[g], ps[0][a], ps[1][a], -z)
            c.add(-ops[g], -ps[0][a], z)
            c.add(-ops[g], -ps[1][a], z)
        for e in active_pairs:
            a, b = edges[e]
            cross = c.or_(c.and_(ps[0][a], ps[1][b]), c.and_(ps[0][b], ps[1][a]))
            z = pair[n + g][e]
            c.equivalent_if(-ops[g], z, cross)
            c.add(-ops[g], pp[0][e], pp[1][e], -z)
            c.add(-ops[g], -pp[0][e], z)
            c.add(-ops[g], -pp[1][e], z)
    for g in range(k - roots):
        c.add(*(selectors[h][b][n + g] for h in range(g + 1, k) for b in range(2)))
    # Designated outputs are incomparable: no output wire is read by another output.
    for g in root_indices:
        for h in range(g + 1, k):
            for b in range(2):
                c.add(-selectors[h][b][n + g])
    if ordered:
        # Topologically select the available gate with smallest (max input, min input, op).
        # Newly available gates read the just-produced wire, so their max input is larger.
        for g in range(k - 1):
            if g == k - roots - 1:
                continue
            for b in range(n + g):
                for smaller_b in range(b):
                    c.add(-selectors[g][1][b], -selectors[g + 1][1][smaller_b])
                for a in range(b + 1):
                    for smaller_a in range(a):
                        c.add(-selectors[g][1][b], -selectors[g + 1][1][b],
                              -selectors[g][0][a], -selectors[g + 1][0][smaller_a])
                    c.add(-selectors[g][1][b], -selectors[g + 1][1][b],
                          -selectors[g][0][a], -selectors[g + 1][0][a], -ops[g], ops[g + 1])
    if support is not None:
        for a in support:
            c.add(*(selectors[g][b][a] for g in range(k) for b in range(2)))
        if k - len(support) + roots == 1:
            # Exactly one arc remains beyond one reader per used nonoutput wire.
            used_wires = support + list(range(n, n + k - roots))
            repeated = [c.var() for _ in used_wires]
            c.exactly_one(repeated)
            for w, repeat in zip(used_wires, repeated):
                readers = [selectors[g][b][w] for g in range(k) for b in range(2) if w < n + g]
                for a, b in combinations(readers, 2):
                    c.add(-a, -b, repeat)
                for a, b, z in combinations(readers, 3):
                    c.add(-a, -b, -z)
        elif fanout_budget:
            # Every used nonoutput wire is read at least once; outputs have no readers.
            budget = k - len(support) + roots
            assert budget >= 0
            extras = []
            for w in support + list(range(n, n + k - roots)):
                readers = [selectors[g][b][w] for g in range(k) for b in range(2) if w < n + g]
                thresholds = c.lower_thresholds(readers, budget + 2)
                c.add(-thresholds[budget + 2])
                extras.extend(thresholds[2:budget + 2])
            global_thresholds = c.lower_thresholds(extras, budget + 1)
            c.add(-global_thresholds[budget + 1])
    per_root_accepts = []
    for g in root_indices:
        c.add(-ops[g])
        for r in range(len(independent)):
            c.add(-vals[n + g][r])
        for r, assignment in enumerate(rows):
            if assignment.bit_count() <= 1:
                c.add(-vals[n + g][r])
        per_root_accepts.append(vals[n + g][len(independent):len(independent) + len(edges)])
    accepts = []
    for e in range(len(edges)):
        x = -1
        for ar in per_root_accepts:
            x = c.or_(x, ar[e])
        accepts.append(x)
    if support is not None:
        for x, (a, b) in zip(accepts, edges):
            if a not in allowed or b not in allowed:
                c.add(-x)
    c.at_least(accepts, minimum)
    if omitted is not None:
        c.add(-accepts[edges.index(tuple(omitted))])
    # Vertex cover of the residual graph witnesses the strict target violation.
    cover = [c.var() for _ in range(n)]
    for x, (a, b) in zip(accepts, edges):
        c.add(x, cover[a], cover[b])
    if violation:
        c.at_least(accepts + [-x for x in cover], k + roots + 8)
    minimal_patterns = None
    if patterns:
        assert support is not None and violation
        internal = [e for e, (a, b) in enumerate(edges) if a in allowed and b in allowed]
        def residual_cover_number(deleted):
            adjacent = {a: [] for a in range(7)}
            for e, (a, b) in enumerate(edges):
                if not (deleted >> e & 1):
                    adjacent[a].append(b)
            matched = {}
            def augment(a, seen):
                for b in adjacent[a]:
                    if b in seen:
                        continue
                    seen.add(b)
                    if b not in matched or augment(matched[b], seen):
                        matched[b] = a
                        return True
                return False
            cardinal = sum(augment(a, set()) for a in adjacent)
            assert cardinal == len(matched) == len(set(matched.values()))
            left_reached = set(adjacent) - set(matched.values())
            right_reached = set()
            queue = list(left_reached)
            while queue:
                a = queue.pop()
                for b in adjacent[a]:
                    if matched.get(b) == a or b in right_reached:
                        continue
                    right_reached.add(b)
                    if b in matched and matched[b] not in left_reached:
                        left_reached.add(matched[b])
                        queue.append(matched[b])
            certificate = (set(adjacent) - left_reached) | right_reached
            assert len(certificate) == cardinal
            assert all(a in certificate or b in certificate for a in adjacent for b in adjacent[a])
            assert all(a in adjacent and b in adjacent[a] for b, a in matched.items())
            return cardinal
        acceptable = set()
        for bits in range(1 << len(internal)):
            deleted = sum(1 << e for j, e in enumerate(internal) if bits >> j & 1)
            if bits.bit_count() + 7 > k + roots + residual_cover_number(deleted):
                acceptable.add(bits)
        minimal_patterns = [bits for bits in sorted(acceptable)
            if all((bits ^ (1 << j)) not in acceptable for j in range(len(internal)) if bits >> j & 1)]
        choices = [c.var() for _ in minimal_patterns]
        c.add(*choices)
        for choice, bits in zip(choices, minimal_patterns):
            for j, e in enumerate(internal):
                if bits >> j & 1:
                    c.add(-choice, accepts[e])
    if core:
        for g, ar in zip(root_indices, per_root_accepts):
            c.add(*(c.and_(x, -r) for x, r in zip(ar, pair[n + g])))
            c.add(*(ports[g][b][r] for b in range(2) for r in range(len(independent))))
    Path(stem + '.cnf').write_text('p cnf %d %d\n' % (c.n, len(c.clauses)) +
        ''.join(' '.join(map(str, xs)) + ' 0\n' for xs in c.clauses))
    data = dict(n=n, k=k, roots=roots, root_indices=root_indices, accepts=accepts, minimum=minimum, core=core, support=support, violation=violation, omitted=omitted, ordered=ordered, projected=projected, patterns=patterns, minimal_patterns=minimal_patterns, fanout_budget=fanout_budget,
                edges=edges, independent=independent, rows=rows,
                ops=ops, selectors=selectors, vals=vals, pair=pair, cover=cover,
                variables=c.n, clauses=len(c.clauses))
    Path(stem + '.json').write_text(json.dumps(data))
    print(json.dumps({x: data[x] for x in ['k', 'minimum', 'core', 'support', 'variables', 'clauses']}))


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--gates', type=int, required=True)
    p.add_argument('--minimum', type=int, default=0)
    p.add_argument('--no-core', action='store_true')
    p.add_argument('--support')
    p.add_argument('--no-violation', action='store_true')
    p.add_argument('--omit-edge')
    p.add_argument('--ordered', action='store_true')
    p.add_argument('--projected', action='store_true')
    p.add_argument('--patterns', action='store_true')
    p.add_argument('--fanout-budget', action='store_true')
    p.add_argument('--roots', type=int, default=2)
    p.add_argument('--stem', required=True)
    a = p.parse_args()
    support = None if a.support is None else [int(x) for x in a.support.split(',')]
    omitted = None if a.omit_edge is None else [int(x) for x in a.omit_edge.split(',')]
    generate(a.gates, a.minimum, not a.no_core, support, a.stem, not a.no_violation, omitted, a.ordered, a.projected, a.patterns, a.fanout_budget, a.roots)
