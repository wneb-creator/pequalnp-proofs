#!/usr/bin/env python3
"""Exact monotone two-input circuit synthesis on characterizing assignments.

No conclusion about Lean acceptance is implied by a SAT/UNSAT answer.
All selected inputs precede their gate; repeated operands are allowed.
Only safe symmetries are used: ordered operands, final output, and live gates.
The latter is complete for at-most-k circuits because unused gates can first
be removed, then identical-operand copies appended to reach k gates.
"""

from __future__ import annotations

import argparse
import datetime
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, "/tmp/oec/pequalnp-pilot-137/z3-package")
import z3


def graph(problem: str):
    if problem == "fano":
        return 14, [(p, 7 + l) for p in range(7) for l in range(7)
                    if (p - l) % 7 in (0, 1, 3)]
    if problem == "p4":
        return 4, [(0, 1), (1, 2), (2, 3)]
    if problem == "c4":
        return 4, [(0, 2), (0, 3), (1, 2), (1, 3)]
    raise ValueError(problem)


def characterizing_assignments(n, edges):
    edge_masks = [(1 << a) | (1 << b) for a, b in edges]

    def target(x):
        return any(x & e == e for e in edge_masks)

    maximal_false = []
    for x in range(1 << n):
        if not target(x) and all(target(x | (1 << i))
                                 for i in range(n) if not (x >> i) & 1):
            maximal_false.append(x)
    tests = edge_masks + maximal_false
    expected = [True] * len(edge_masks) + [False] * len(maximal_false)
    # Independently verify the antichain description on every assignment.
    for x in range(1 << n):
        below_true = any(x & a == a for a in edge_masks)
        above_false = any(x & a == x for a in maximal_false)
        assert below_true == target(x)
        assert above_false != target(x)
    return tests, expected, target


def known_seed(problem):
    if problem == "p4":
        return [(False, 0, 2), (True, 1, 4),
                (True, 2, 3), (False, 5, 6)]
    if problem == "c4":
        return [(False, 0, 1), (False, 2, 3), (True, 4, 5)]
    if problem == "fano":
        gates = []
        stars = []
        for l in range(7):
            ps = [p for p in range(7) if (p - l) % 7 in (0, 1, 3)]
            gates.append((False, ps[0], ps[1]))
            a = 14 + len(gates) - 1
            gates.append((False, ps[2], a))
            a = 14 + len(gates) - 1
            gates.append((True, 7 + l, a))
            stars.append(14 + len(gates) - 1)
        a = stars[0]
        for b in stars[1:]:
            gates.append((False, a, b))
            a = 14 + len(gates) - 1
        return [(op, min(a, b), max(a, b)) for op, a, b in gates]
    raise ValueError(problem)


def eval_circuit(n, gates, x):
    values = [bool((x >> i) & 1) for i in range(n)]
    for op, a, b in gates:
        values.append(values[a] and values[b] if op else values[a] or values[b])
    return values[-1]


def synthesize(args):
    n, edges = graph(args.problem)
    tests, expected, target = characterizing_assignments(n, edges)
    k = args.gates
    assert k > 0
    solver = z3.SolverFor("QF_FD")
    solver.set(timeout=args.timeout_ms)
    solver.set(random_seed=args.seed)
    clauses = []
    select = []
    ops = []
    values = []

    def clause(*lits):
        clauses.append(z3.Or(*lits))

    def exactly_one(xs):
        clause(*xs)
        for i, a in enumerate(xs):
            for b in xs[i + 1:]:
                clause(z3.Not(a), z3.Not(b))

    for g in range(k):
        width = n + g
        ss = [[z3.Bool(f"s_{g}_{side}_{i}") for i in range(width)]
              for side in range(2)]
        select.append(ss)
        for side in range(2):
            exactly_one(ss[side])
        # AND and OR commute, so left <= right preserves completeness.
        for a in range(width):
            for b in range(a):
                clause(z3.Not(ss[0][a]), z3.Not(ss[1][b]))
        op = z3.Bool(f"and_{g}")
        ops.append(op)
        vv = [z3.Bool(f"v_{g}_{t}") for t in range(len(tests))]
        values.append(vv)
        uu = [[z3.Bool(f"u_{g}_{side}_{t}") for t in range(len(tests))]
              for side in range(2)]
        for side in range(2):
            for i, s in enumerate(ss[side]):
                for t, x in enumerate(tests):
                    u = uu[side][t]
                    if i < n:
                        clause(z3.Not(s), u if (x >> i) & 1 else z3.Not(u))
                    else:
                        v = values[i - n][t]
                        clause(z3.Not(s), z3.Not(u), v)
                        clause(z3.Not(s), u, z3.Not(v))
        for t, y in enumerate(vv):
            u, v = uu[0][t], uu[1][t]
            # op -> y = (u AND v)
            clause(z3.Not(op), z3.Not(y), u)
            clause(z3.Not(op), z3.Not(y), v)
            clause(z3.Not(op), y, z3.Not(u), z3.Not(v))
            # not op -> y = (u OR v)
            clause(op, z3.Not(u), y)
            clause(op, z3.Not(v), y)
            clause(op, z3.Not(y), u, v)
    for t, value in enumerate(expected):
        clause(values[-1][t] if value else z3.Not(values[-1][t]))

    if not args.allow_dead:
        for g in range(k - 1):
            clause(*(select[j][side][n + g]
                     for j in range(g + 1, k) for side in range(2)))

    if args.fixed_seed:
        seed = known_seed(args.problem)
        assert len(seed) <= k
        while len(seed) < k:
            w = n + len(seed) - 1
            seed.append((False, w, w))
        for g, (op, a, b) in enumerate(seed):
            clause(ops[g] if op else z3.Not(ops[g]))
            clause(select[g][0][min(a, b)])
            clause(select[g][1][max(a, b)])

    solver.add(*clauses)
    start = time.monotonic()
    print(json.dumps({"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                      "problem": args.problem, "gates": k,
                      "tests": len(tests), "clauses": len(clauses),
                      "z3": z3.get_version_string(), "fixed_seed": args.fixed_seed,
                      "allow_dead": args.allow_dead, "seed": args.seed}), flush=True)
    result = solver.check()
    record = {"result": str(result), "elapsed_seconds": time.monotonic() - start,
              "problem": args.problem, "gates": k, "tests": len(tests),
              "clauses": len(clauses), "z3": z3.get_version_string(),
              "fixed_seed": args.fixed_seed, "allow_dead": args.allow_dead,
              "seed": args.seed, "statistics": str(solver.statistics())}
    if result == z3.sat:
        model = solver.model()
        gates = []
        for g in range(k):
            picks = []
            for side in range(2):
                selected = [i for i, s in enumerate(select[g][side])
                            if z3.is_true(model.eval(s, model_completion=True))]
                assert len(selected) == 1
                picks.append(selected[0])
            op = z3.is_true(model.eval(ops[g], model_completion=True))
            gates.append((op, *picks))
        for x in range(1 << n):
            assert eval_circuit(n, gates, x) == target(x), (x, gates)
        record["gates_data"] = gates
        record["full_truth_table_verified"] = 1 << n
    elif result == z3.unknown:
        record["reason_unknown"] = solver.reason_unknown()
    print(json.dumps(record, indent=2), flush=True)
    if args.output:
        Path(args.output).write_text(json.dumps(record, indent=2) + "\n")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--problem", choices=["fano", "p4", "c4"], default="fano")
    ap.add_argument("--gates", type=int, required=True)
    ap.add_argument("--timeout-ms", type=int, default=60000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--fixed-seed", action="store_true")
    ap.add_argument("--allow-dead", action="store_true")
    ap.add_argument("--output")
    args = ap.parse_args()
    return synthesize(args)


if __name__ == "__main__":
    raise SystemExit(main())
