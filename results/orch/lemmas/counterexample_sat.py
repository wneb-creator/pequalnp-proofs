"""SAT search for a small binary monotone circuit for an edge function.

Positive edge inputs and negative maximal independent sets suffice by
monotonicity. A found circuit is separately reevaluated on every input.
Duplicate operands permit padding, so a k-gate search also covers fewer gates.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path
import subprocess
import time

from counterexample_small import star_profile


class CNF:
    def __init__(self):
        self.names = [None, "true"]
        self.clauses = [[1]]

    def var(self, name):
        self.names.append(name)
        return len(self.names) - 1

    def add(self, *clause):
        self.clauses.append(list(clause))

    def exactly_one(self, variables):
        self.add(*variables)
        for x, y in combinations(variables, 2):
            self.add(-x, -y)

    def save(self, path):
        with path.open("w") as f:
            f.write(f"p cnf {len(self.names)-1} {len(self.clauses)}\n")
            for clause in self.clauses:
                f.write(" ".join(map(str, clause)) + " 0\n")


def critical_inputs(n, edges):
    def target(x):
        return any(x >> a & x >> b & 1 for a, b in edges)
    positive = {1 << a | 1 << b for a, b in edges}
    negative = {x for x in range(1 << n) if not target(x)
                and all(x >> i & 1 or target(x | 1 << i) for i in range(n))}
    assert not positive & negative
    return [(x, False) for x in sorted(negative)] + [(x, True) for x in sorted(positive)]


def encode(n, edges, k, ordered):
    m = CNF()
    tests = critical_inputs(n, edges)
    wires = [[1 if x >> i & 1 else -1 for x, _ in tests] for i in range(n)]
    gates = []
    for t in range(k):
        op = m.var((t, "and"))
        sel = [[m.var((t, p, i)) for i in range(n + t)] for p in range(2)]
        for s in sel:
            m.exactly_one(s)
        # Gate operations commute. Equality allows redundant padding gates.
        for i in range(n + t):
            for j in range(i):
                m.add(-sel[0][i], -sel[1][j])
        if ordered and t:
            prev = gates[-1][1]
            dependent = sel[1][n + t - 1]
            # Adjacent independent gates admit lexicographic input ordering.
            for i in range(n + t - 1):
                for j in range(i):
                    m.add(-prev[0][i], -sel[0][j], dependent)
        output = []
        for row, (x, _) in enumerate(tests):
            vals = []
            for p in range(2):
                v = m.var((t, p, "input", x))
                vals.append(v)
                for i, s in enumerate(sel[p]):
                    src = wires[i][row]
                    m.add(-s, -v, src)
                    m.add(-s, v, -src)
            a, b = vals
            y = m.var((t, "output", x))
            output.append(y)
            m.add(-op, -y, a)
            m.add(-op, -y, b)
            m.add(y, -a, -b)
            m.add(op, y, -a)
            m.add(op, y, -b)
            m.add(-y, a, b)
        gates.append((op, sel))
        wires.append(output)
    for row, (_, target) in enumerate(tests):
        m.add(wires[-1][row] if target else -wires[-1][row])
    for t in range(k - 1):
        m.add(*[s[n + t] for _, sel in gates[t + 1:] for s in sel])
    return m, gates, tests


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, required=True)
    p.add_argument("--gates", type=int, required=True)
    p.add_argument("--edges", required=True)
    p.add_argument("--seconds", type=int, default=300)
    p.add_argument("--ordered", action="store_true")
    p.add_argument("--prefix", required=True)
    p.add_argument("--solver", required=True)
    a = p.parse_args()
    start = time.monotonic()
    edges = json.loads(a.edges)
    model, gates, tests = encode(a.n, edges, a.gates, a.ordered)
    prefix = Path(a.prefix)
    cnf = prefix.with_suffix(".cnf")
    sol = prefix.with_suffix(".solution")
    model.save(cnf)
    report = {"n": a.n, "edges": edges, "gates": a.gates,
              "tests": tests, "variables": len(model.names)-1,
              "clauses": len(model.clauses), "ordered": a.ordered}
    print(json.dumps(report), flush=True)
    with prefix.with_suffix(".solver.stdout").open("w") as out, \
            prefix.with_suffix(".solver.stderr").open("w") as err:
        run = subprocess.run([a.solver, "-t", str(a.seconds), "-w", str(sol), str(cnf)],
                             stdout=out, stderr=err)
    report["exit"] = run.returncode
    report["elapsed"] = time.monotonic()-start
    if run.returncode == 10:
        values = set()
        for line in sol.read_text().splitlines():
            if line.startswith("v "):
                values.update(int(v) for v in line.split()[1:] if int(v) > 0)
        program = []
        for op, sel in gates:
            operands = []
            for s in sel:
                found = [i for i, v in enumerate(s) if v in values]
                assert len(found) == 1, found
                operands.append(found[0])
            program.append(("and" if op in values else "or", *operands))
        for x in range(1 << a.n):
            w = [bool(x >> i & 1) for i in range(a.n)]
            for op, i, j in program:
                w.append(w[i] and w[j] if op == "and" else w[i] or w[j])
            expected = any(x >> u & x >> v & 1 for u, v in edges)
            assert w[-1] == expected, (x, program)
        report["program"] = program
        report["star"], report["owned"] = star_profile(a.n, edges, program)
    prefix.with_suffix(".json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
