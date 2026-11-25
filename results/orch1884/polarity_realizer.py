"""Realize a signed binary DAG using AND/OR and at most one paid NOT.

Input gates are (kind, left, right), where kinds 0,1,2,3 mean
AND, OR, AND-NOT-right, and AND-NOT-left. Primary wire free_neg
has both polarities supplied; all other primary wires start positive.
"""

from itertools import product
import random


class XorComponents:
    def __init__(self, n):
        self.parent = list(range(n))
        self.parity = [0] * n
        self.rank = [0] * n

    def find(self, v):
        if self.parent[v] != v:
            parent, parity = self.find(self.parent[v])
            self.parity[v] ^= parity
            self.parent[v] = parent
        return self.parent[v], self.parity[v]

    def add(self, u, v, parity):
        ru, pu = self.find(u)
        rv, pv = self.find(v)
        if ru == rv:
            return pu ^ pv == parity
        if self.rank[ru] < self.rank[rv]:
            ru, rv = rv, ru
        self.parent[rv] = ru
        self.parity[rv] = pu ^ pv ^ parity
        if self.rank[ru] == self.rank[rv]:
            self.rank[ru] += 1
        return True


def realize(n, gates, free_neg=0, output=None):
    assert 0 <= free_neg < n
    size = n + len(gates)
    if output is None:
        output = size - 1
    assert 0 <= output < size
    for i, (kind, a, b) in enumerate(gates):
        assert kind in range(4) and 0 <= a < n + i and 0 <= b < n + i
    for paid in [None] + [v for v in range(size) if v != free_neg]:
        uf = XorComponents(size + 1)
        anchor = size
        good = all(uf.add(i, anchor, 0) for i in range(n))
        if output != paid and output != free_neg:
            good = good and uf.add(output, anchor, 0)
        for i, (kind, a, b) in enumerate(gates):
            for source, flip in [(a, int(kind == 3)), (b, int(kind == 2))]:
                if source not in (free_neg, paid):
                    good = good and uf.add(source, n + i, flip)
        if not good:
            continue
        anchored_root, anchored_parity = uf.find(anchor)
        polarity = []
        for v in range(size):
            root, parity = uf.find(v)
            polarity.append(parity ^ (anchored_parity if root == anchored_root else 0))
        actual = []
        wires = {(i, 0): i for i in range(n)}
        wires[free_neg, 1] = n

        def add_not(v, base):
            index = n + 1 + len(actual)
            actual.append(("not", wires[v, base]))
            wires[v, 1 - base] = index

        if paid is not None and paid < n:
            add_not(paid, 0)
        for i, (kind, a, b) in enumerate(gates):
            v = n + i
            sign = polarity[v]
            a_sign = sign ^ int(kind == 3)
            b_sign = sign ^ int(kind == 2)
            op = "or" if (kind == 1) ^ bool(sign) else "and"
            index = n + 1 + len(actual)
            actual.append((op, wires[a, a_sign], wires[b, b_sign]))
            wires[v, sign] = index
            if paid == v:
                add_not(v, sign)
        return {"gates": actual, "output": wires[output, 0],
                "paid_wire": paid, "polarity": polarity, "free_neg": free_neg}
    return None


def signed_eval(n, gates, x, output=None):
    w = list(x)
    for kind, a, b in gates:
        aa, bb = w[a], w[b]
        w.append((aa and bb) if kind == 0 else (aa or bb) if kind == 1
                 else (aa and not bb) if kind == 2 else (not aa and bb))
    return w[len(w) - 1 if output is None else output]


def actual_eval(n, witness, x):
    w = list(x) + [not x[witness["free_neg"]]]
    for g in witness["gates"]:
        if g[0] == "not":
            w.append(not w[g[1]])
        elif g[0] == "and":
            w.append(w[g[1]] and w[g[2]])
        else:
            w.append(w[g[1]] or w[g[2]])
    return w[witness["output"]]


def brute_feasible(n, gates, free_neg=0):
    for labels in product([0, 1], repeat=len(gates)):
        polarity = [0] * n + list(labels)
        flips = set()
        for i, (kind, a, b) in enumerate(gates):
            sign = polarity[n + i]
            for source, flip in [(a, int(kind == 3)), (b, int(kind == 2))]:
                if source != free_neg and (sign ^ flip) != polarity[source]:
                    flips.add(source)
        if polarity[-1]:
            flips.add(len(polarity) - 1)
        if len(flips) <= 1:
            return True
    return False


def self_test():
    rng = random.Random(1884)
    realized = 0
    rows = 0
    for trial in range(1000):
        n = rng.randrange(2, 6)
        count = rng.randrange(1, 11)
        gates = [(rng.randrange(4), rng.randrange(n + i), rng.randrange(n + i))
                 for i in range(count)]
        witness = realize(n, gates)
        if witness is None:
            continue
        realized += 1
        assert sum(g[0] == "not" for g in witness["gates"]) <= 1
        assert len(witness["gates"]) <= count + 1
        for x in product([False, True], repeat=n):
            assert signed_eval(n, gates, x) == actual_eval(n, witness, x)
            rows += 1
    for trial in range(200):
        n = rng.randrange(2, 5)
        count = rng.randrange(1, 8)
        gates = [(rng.randrange(4), rng.randrange(n + i), rng.randrange(n + i))
                 for i in range(count)]
        free = rng.randrange(n)
        assert (realize(n, gates, free_neg=free) is not None) == brute_feasible(n, gates, free)
    return {"random_traces": 1000, "realized": realized, "truth_rows_checked": rows,
            "exhaustive_polarity_cross_checks": 200}


if __name__ == "__main__":
    print(self_test())
