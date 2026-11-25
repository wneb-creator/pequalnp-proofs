#!/usr/bin/env python3
"""Exact small-instance AND-count search for graph vertex-cover CNFs.

All truth inputs are tested. Singleton stripping permits disjoint bare
variable sets, provided the target rejects every singleton. This is a
computational search aid, not a Lean certificate.
"""
import argparse
import itertools
import json
from pathlib import Path
from signed_code_sat import CNF


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--graphs", type=Path, required=True)
    p.add_argument("--index", type=int, required=True)
    p.add_argument("--vertices", type=int, required=True)
    p.add_argument("--ands", type=int, required=True)
    p.add_argument("--prefix", type=Path, required=True)
    p.add_argument("--decode", type=Path)
    args = p.parse_args()
    graphs = json.loads(args.graphs.read_text())
    assert isinstance(graphs, list)
    graph = graphs[args.index]
    edges = graph["edges"]
    n, k = args.vertices, args.ands
    assert all(len(e) == 2 and 0 <= e[0] < e[1] < n for e in edges)

    def target(x):
        return all(((x >> a) | (x >> b)) & 1 for a, b in edges)

    assert not target(0) and all(not target(1 << i) for i in range(n))
    c = CNF()
    selectors = [[[c.var() for _ in range(n + i)] for _ in range(2)] for i in range(k)]
    outputs = [c.var() for _ in range(k)]
    for i, sides in enumerate(selectors):
        for v in range(n):
            c.add(-sides[0][v], -sides[1][v])
        # Canonical order of the two commutative AND operands.
        prefix = c.var()
        c.add(prefix)
        for a, b in zip(reversed(sides[0]), reversed(sides[1])):
            c.add(-prefix, -a, b)
            equal_next = c.var()
            c.add(-prefix, a, b, equal_next)
            c.add(-prefix, -a, -b, equal_next)
            prefix = equal_next

    for x in range(1 << n):
        values = []
        for i, sides in enumerate(selectors):
            vals = []
            for side in sides:
                terms = [side[v] for v in range(n) if (x >> v) & 1]
                terms.extend(c.conj(side[n + j], values[j]) for j in range(i))
                vals.append(c.disj(terms))
            values.append(c.conj(*vals))
        out = c.disj([c.conj(outputs[j], values[j]) for j in range(k)])
        c.add(out if target(x) else -out)

    metadata = {"vertices": n, "ands": k, "edges": edges,
                "selectors": selectors, "outputs": outputs,
                "variables": c.n, "clauses": len(c.clauses)}
    if args.decode:
        model = set()
        for line in args.decode.read_text().splitlines():
            if line.startswith("v "):
                model.update(int(t) for t in line.split()[1:] if int(t) > 0)
        gates = [[[j for j, v in enumerate(side) if v in model] for side in sides]
                 for sides in selectors]
        out = [i for i, v in enumerate(outputs) if v in model]
        for x in range(1 << n):
            values = [bool((x >> v) & 1) for v in range(n)]
            for left, right in gates:
                values.append(any(values[v] for v in left) and any(values[v] for v in right))
            assert any(values[n + i] for i in out) == target(x)
        print(json.dumps({"edges": edges, "gates": gates, "output_gates": out,
                          "all_truth_rows_verified": 1 << n}, indent=2))
    else:
        with args.prefix.with_suffix(".cnf").open("w") as f:
            f.write(f"p cnf {c.n} {len(c.clauses)}\n")
            for clause in c.clauses:
                f.write(" ".join(map(str, clause)) + " 0\n")
        args.prefix.with_suffix(".meta.json").write_text(json.dumps(metadata, indent=2) + "\n")
        print(json.dumps({k: metadata[k] for k in ("vertices", "ands", "variables", "clauses")}))


if __name__ == "__main__":
    main()
