#!/usr/bin/env python3
"""Search signed partial-assignment separation codes, not Lean proofs."""
import argparse
import itertools
import json
from pathlib import Path


class CNF:
    def __init__(self):
        self.n = 0
        self.clauses = []

    def var(self):
        self.n += 1
        return self.n

    def add(self, *lits):
        self.clauses.append(lits)

    def conj(self, a, b):
        c = self.var()
        self.add(-c, a)
        self.add(-c, b)
        self.add(c, -a, -b)
        return c

    def disj(self, xs):
        c = self.var()
        for x in xs:
            self.add(-x, c)
        self.add(-c, *xs)
        return c

    def at_most(self, xs, limit):
        # Small one-hot threshold DP, linear in len(xs) * limit.
        old = []
        for i, x in enumerate(xs):
            new = []
            for j in range(min(i + 1, limit + 1)):
                a = old[j] if j < len(old) else None
                b = x if j == 0 else self.conj(x, old[j - 1])
                new.append(b if a is None else self.disj([a, b]))
            old = new
        if len(old) > limit:
            self.add(-old[limit])


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--words", type=int, required=True)
    p.add_argument("--coords", type=int, required=True)
    p.add_argument("--width", type=int, required=True)
    p.add_argument("--separate", type=int, required=True)
    p.add_argument("--pair-union", type=int)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--decode", type=Path)
    args = p.parse_args()
    n, d = args.words, args.coords
    c = CNF()
    words = [[[c.var(), c.var()] for _ in range(d)] for _ in range(n)]
    supports = []
    for word in words:
        supp = []
        for pair in word:
            c.add(-pair[0], -pair[1])
            supp.append(c.disj(pair))
        supports.append(supp)
        c.at_most(supp, args.width)

    # Empty-set separating assignment can be assumed all-positive.
    for word in words:
        c.add(*(pair[1] for pair in word))

    if args.pair_union is not None:
        for a, b in itertools.combinations(range(n), 2):
            union = [c.disj([supports[a][i], supports[b][i]]) for i in range(d)]
            c.at_most(union, args.pair_union)

    for r in range(1, args.separate + 1):
        for selected in itertools.combinations(range(n), r):
            picked = set(selected)
            f = [[c.var(), c.var()] for _ in range(d)]
            for pair in f:
                c.add(-pair[0], -pair[1])
            for w in range(n):
                if w in picked:
                    for i in range(d):
                        for sign in range(2):
                            c.add(-words[w][i][sign], -f[i][sign])
                else:
                    hits = [c.conj(words[w][i][sign], f[i][sign])
                            for i in range(d) for sign in range(2)]
                    c.add(*hits)

    if args.decode:
        model = set()
        for line in args.decode.read_text().splitlines():
            if line.startswith("v "):
                model.update(int(t) for t in line.split()[1:] if int(t) > 0)
        result = []
        for word in words:
            result.append([[i, sign] for i, pair in enumerate(word)
                           for sign, var in enumerate(pair) if var in model])
        # Check the actual intended property independently by exhaustive
        # ternary assignments; intended only for small decoded examples.
        if d <= 8:
            realized = set()
            sets = [set(map(tuple, word)) for word in result]
            for assignment in itertools.product((-1, 0, 1), repeat=d):
                lits = {(i, x) for i, x in enumerate(assignment) if x != -1}
                realized.add(tuple(i for i, word in enumerate(sets) if not (word & lits)))
            wanted = [t for r in range(args.separate + 1)
                      for t in itertools.combinations(range(n), r)]
            assert all(t in realized for t in wanted)
        print(json.dumps({"words": result, "coords": d, "width": args.width,
                          "separate": args.separate}, indent=2))
    else:
        with args.out.open("w") as f:
            f.write(f"p cnf {c.n} {len(c.clauses)}\n")
            for clause in c.clauses:
                f.write(" ".join(map(str, clause)) + " 0\n")
        print(json.dumps({"variables": c.n, "clauses": len(c.clauses),
                          "path": str(args.out)}))


if __name__ == "__main__":
    main()
