"""Bounded binary monotone-circuit search using an installed MILP solver.

This is exploratory only: all witnesses are reevaluated, and infeasibility is
not a Lean certificate. Constants and unary gates are omitted because they are
redundant in a minimum circuit for a nonconstant edge function.
"""
from itertools import combinations
import argparse
import json
import time
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

from counterexample_small import star_profile


class Model:
    def __init__(self):
        self.variables = []
        self.rows = []
        self.lo = []
        self.hi = []

    def var(self, name):
        v = len(self.variables)
        self.variables.append(name)
        return {v: 1.0}

    def constraint(self, terms, lo=-np.inf, hi=np.inf):
        terms = dict(terms)
        const = terms.pop(-1, 0.0)
        self.rows.append(terms)
        self.lo.append(lo - const)
        self.hi.append(hi - const)

    def solve(self, seconds):
        ri, ci, da = [], [], []
        for r, row in enumerate(self.rows):
            for c, val in row.items():
                if val:
                    ri.append(r)
                    ci.append(c)
                    da.append(val)
        mat = coo_matrix((da, (ri, ci)), shape=(len(self.rows), len(self.variables))).tocsc()
        # HiGHS expects C int sparse indices in the installed SciPy.
        mat.indices = mat.indices.astype(np.int32)
        mat.indptr = mat.indptr.astype(np.int32)
        print(json.dumps({"variables": len(self.variables), "constraints": len(self.rows)}), flush=True)
        return milp(np.zeros(len(self.variables)), integrality=np.ones(len(self.variables)),
                    bounds=Bounds(0, 1),
                    constraints=LinearConstraint(mat, np.array(self.lo), np.array(self.hi)),
                    options={"time_limit": seconds, "disp": True})


def lin(*terms):
    out = {}
    for factor, expr in terms:
        for v, c in expr.items():
            out[v] = out.get(v, 0.0) + factor * c
    return out


def circuit_model(n, edges, k, first_zero=False):
    m = Model()
    inputs = [[{-1: float(x >> i & 1)} for x in range(1 << n)] for i in range(n)]
    wires = list(inputs)
    gates = []
    for t in range(k):
        op = m.var((t, "and"))
        sel = [[m.var((t, port, i)) for i in range(n + t)] for port in range(2)]
        for s in sel:
            m.constraint(lin(*[(1, x) for x in s]), lo=1, hi=1)
        m.constraint(lin(*[(i, x) for i, x in enumerate(sel[0])],
                         *[(-i, x) for i, x in enumerate(sel[1])]), hi=-1)
        if t == 0 and first_zero:
            m.constraint(sel[0][0], lo=1, hi=1)
        out = []
        for assignment in range(1 << n):
            values = []
            for p in range(2):
                val = m.var((t, p, "input", assignment))
                values.append(val)
                for i, s in enumerate(sel[p]):
                    source = wires[i][assignment]
                    m.constraint(lin((1, val), (-1, source), (1, s)), hi=1)
                    m.constraint(lin((-1, val), (1, source), (1, s)), hi=1)
            a, b = values
            y = m.var((t, "output", assignment))
            out.append(y)
            m.constraint(lin((1, y), (-1, a), (1, op)), hi=1)
            m.constraint(lin((1, y), (-1, b), (1, op)), hi=1)
            m.constraint(lin((-1, y), (1, a), (1, b)), hi=1)
            m.constraint(lin((-1, y), (1, a), (-1, op)), hi=0)
            m.constraint(lin((-1, y), (1, b), (-1, op)), hi=0)
            m.constraint(lin((1, y), (-1, a), (-1, b)), hi=0)
        wires.append(out)
        gates.append((op, sel))
    for x in range(1 << n):
        target = int(any(x >> a & x >> b & 1 for a, b in edges))
        m.constraint(wires[-1][x], lo=target, hi=target)
    # A minimum circuit cannot carry a dead gate.
    for t in range(k - 1):
        uses = [s[n + t] for _, sel in gates[t + 1:] for s in sel]
        m.constraint(lin(*[(1, s) for s in uses]), lo=1)
    return m, gates


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, default=5)
    p.add_argument("--gates", type=int, default=6)
    p.add_argument("--seconds", type=float, default=300)
    p.add_argument("--edges", type=str)
    p.add_argument("--first-zero", action="store_true")
    p.add_argument("--fixed", type=str,
                   help="JSON list of fixed initial gates [operation,input,input]")
    a = p.parse_args()
    edges = json.loads(a.edges) if a.edges else [(i, (i + 1) % a.n) for i in range(a.n)]
    start = time.monotonic()
    m, gs = circuit_model(a.n, edges, a.gates, a.first_zero)
    if a.fixed:
        for t, (operation, i, j) in enumerate(json.loads(a.fixed)):
            op, sel = gs[t]
            bit = int(operation == "and")
            m.constraint(op, lo=bit, hi=bit)
            m.constraint(sel[0][i], lo=1, hi=1)
            m.constraint(sel[1][j], lo=1, hi=1)
    result = m.solve(a.seconds)
    report = {"n": a.n, "edges": edges, "gates": a.gates, "status": int(result.status),
              "message": result.message, "elapsed": time.monotonic() - start}
    if result.x is not None:
        def val(expr):
            return sum(float(result.x[v]) * c for v, c in expr.items())
        program = []
        for op, sel in gs:
            operands = [max(range(len(s)), key=lambda i: val(s[i])) for s in sel]
            program.append(("and" if val(op) > .5 else "or", *operands))
        actual = []
        for x in range(1 << a.n):
            w = [bool(x >> i & 1) for i in range(a.n)]
            for op, i, j in program:
                w.append(w[i] and w[j] if op == "and" else w[i] or w[j])
            expected = any(x >> u & x >> v & 1 for u, v in edges)
            assert w[-1] == expected, (x, program)
            actual.append(w[-1])
        report["program"] = program
        report["star"], report["owned"] = star_profile(a.n, edges, program)
    print(json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
