#!/usr/bin/env python3
"""Necessary signed-code conditions for twelve-AND plane circuits.

This is a search aid only; a SAT result is not a circuit or a Lean proof.
"""
import argparse
import itertools
import json
from pathlib import Path
from signed_code_sat import CNF


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--rows", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--fixed-cycle", action="store_true")
    p.add_argument("--width", type=int, default=4)
    p.add_argument("--no-pair-cuts", action="store_true")
    p.add_argument("--decode", type=Path)
    args = p.parse_args()
    rows = json.loads(args.rows.read_text())["rows"]
    assert len(rows) == 704 and all(len(row) == 2 for row in rows)
    c = CNF()
    d = 12
    words = [[[c.var(), c.var()] for _ in range(d)] for _ in range(26)]
    supports = []
    for word in words:
        supp = []
        for pair in word:
            c.add(-pair[0], -pair[1])
            supp.append(c.disj(pair))
        supports.append(supp)
        c.at_most(supp, args.width)
    for a, b in itertools.combinations(range(26), 2):
        same_side = (a < 13) == (b < 13)
        incident = not same_side and (a - (b - 13)) % 13 in (0, 1, 3, 9)
        if incident or args.no_pair_cuts:
            continue
        union = [c.disj([supports[a][i], supports[b][i]]) for i in range(d)]
        c.at_most(union, 6 if same_side else 5)

    if args.fixed_cycle:
        fixed = {
            1: [(2, 0), (3, 1)],
            0: [(0, 1), (1, 1), (2, 1), (3, 1)],
            4: [(0, 1), (1, 0)],
            6: [(1, 1), (3, 0)],
            2: [(0, 0), (2, 1)],
        }
        rest = [i for i in range(13) if i not in fixed]
        for coord, v in enumerate(rest, start=4):
            fixed[v] = [(coord, 1)]
        for v, lits in fixed.items():
            for i in range(d):
                for sign in range(2):
                    c.add(words[v][i][sign] if (i, sign) in lits else -words[v][i][sign])

    for point_mask, line_mask in rows:
        selected = {i for i in range(13) if (point_mask >> i) & 1}
        selected.update(13 + i for i in range(13) if (line_mask >> i) & 1)
        f = [[c.var(), c.var()] for _ in range(d)]
        for pair in f:
            c.add(-pair[0], -pair[1])
        for w in range(26):
            if w in selected:
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
        result = [[[i, sign] for i, pair in enumerate(word)
                   for sign, var in enumerate(pair) if var in model] for word in words]
        print(json.dumps({"words": result, "coords": d, "rows": len(rows)}, indent=2))
    else:
        with args.out.open("w") as f:
            f.write(f"p cnf {c.n} {len(c.clauses)}\n")
            for clause in c.clauses:
                f.write(" ".join(map(str, clause)) + " 0\n")
        print(json.dumps({"variables": c.n, "clauses": len(c.clauses), "out": str(args.out)}))


if __name__ == "__main__":
    main()
