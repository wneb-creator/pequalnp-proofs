"""Independently reconstruct archived CNFs and validate SAT witnesses.

This checks encodings and SAT models; it does not certify solver UNSAT verdicts.
Run from the repository root with Python 3.
"""

from pathlib import Path
import json


def reconstruct(n, k, rows, variant):
    count = 0
    clauses = []

    def fresh():
        nonlocal count
        count += 1
        return count

    def add(*literals):
        clauses.append(tuple(literals))

    def conjunction(a, b):
        z = fresh()
        add(-z, a)
        add(-z, b)
        add(z, -a, -b)
        return z

    def disjunction(z, terms):
        for term in terms:
            add(-term, z)
        add(-z, *terms)

    selectors = [[[fresh() for _ in range(n + i)] for _ in range(2)] for i in range(k)]
    outputs = [fresh() for _ in range(k)]
    if variant != "base":
        for left, right in selectors:
            for a, b in zip(left, right):
                add(-a, -b)
            if variant in ("ordered", "top"):
                for j, b in enumerate(right):
                    add(-b, *left[:j])
    all_values = []
    for point, answer in rows:
        values = []
        for i in range(k):
            sides = []
            for side in range(2):
                terms = []
                for j, selector in enumerate(selectors[i][side]):
                    if j < n:
                        if point >> j & 1:
                            terms.append(selector)
                    else:
                        terms.append(conjunction(selector, values[j - n]))
                z = fresh()
                disjunction(z, terms)
                sides.append(z)
            values.append(conjunction(*sides))
        if answer:
            add(*[conjunction(s, v) for s, v in zip(outputs, values)])
        else:
            for selector, value in zip(outputs, values):
                add(-selector, -value)
        all_values.append(values)
    if variant == "top":
        negatives = [t for t, (_, answer) in enumerate(rows) if not answer]
        for i, selector in enumerate(outputs):
            add(selector, *[all_values[t][i] for t in negatives])
            for j in range(i + 1, k):
                for side in range(2):
                    add(-selector, -selectors[j][side][n + i])
    return count, clauses


def main():
    directory = Path("results/orch/free-or/runs")
    cases = []
    for file in sorted(directory.glob("*.json")):
        data = json.loads(file.read_text())
        if isinstance(data, dict) and "critical_rows" in data:
            cases.append((file.stem, data))
    assert len(cases) == 14
    sat_count = 0
    for stem, data in cases:
        n, edges, k = data["n"], data["edges"], data["ands"]
        dual = data.get("dual", False)

        def graph_value(point):
            return any(point >> a & 1 and point >> b & 1 for a, b in edges)

        independent = [s for s in range(1 << n) if not graph_value(s)]
        maximal = [s for s in independent if not any(t != s and s & t == s for t in independent)]
        rows = [((1 << a) | (1 << b), 1) for a, b in edges] + [(s, 0) for s in maximal]
        if dual:
            rows = [(((1 << n) - 1) ^ s, 1 - answer) for s, answer in rows]
        assert len(rows) == data["critical_rows"]
        lines = (directory / (stem + ".cnf")).read_text().splitlines()
        header = lines[0].split()
        assert all(line.split()[-1] == "0" for line in lines[1:])
        actual = [tuple(map(int, line.split()[:-1])) for line in lines[1:]]
        assert header[:2] == ["p", "cnf"]
        assert int(header[2]) == data["variables"]
        assert int(header[3]) == data["clauses"] == len(actual)
        assert all(1 <= abs(x) <= data["variables"] for clause in actual for x in clause)
        matches = []
        for variant in ("base", "disjoint", "ordered", "top"):
            variables, expected = reconstruct(n, k, rows, variant)
            if variables == data["variables"] and actual == expected:
                matches.append(variant)
        assert len(matches) == 1, (stem, matches)
        solver_lines = (directory / (stem + ".solver.log")).read_text().splitlines()
        statuses = [line for line in solver_lines if line.startswith("s ")]
        assert statuses == data["status"]
        print("EXACT_CNF_PASS", stem, matches[0], "dual", dual,
              "status", statuses, "exit", data["exit"], "seconds", round(data["seconds"], 3))
        if data["exit"] != 10:
            continue
        literals = [int(x) for line in solver_lines if line.startswith("v ")
                    for x in line[2:].split() if x != "0"]
        model = {abs(x): x > 0 for x in literals}
        assert len(model) == data["variables"]
        assert all(any(model[abs(x)] == (x > 0) for x in clause) for clause in actual)
        for point in range(1 << n):
            target = not graph_value(((1 << n) - 1) ^ point) if dual else graph_value(point)
            wires = [bool(point >> i & 1) for i in range(n)]
            for left, right in data["choices"]:
                assert all(0 <= j < len(wires) for j in left + right)
                wires.append(any(wires[j] for j in left) and any(wires[j] for j in right))
            assert any(wires[n + i] for i in data["outputs"]) == target
            wires = [bool(point >> i & 1) for i in range(n)]
            for operation, a, b in data["binary_gates"]:
                assert operation in ("and", "or") and a >= 0 and b >= 0
                assert a < len(wires) or a == n + 1000000
                assert b < len(wires) or b == n + 1000000
                x = wires[a] if a < len(wires) else False
                y = wires[b] if b < len(wires) else False
                wires.append((x and y) if operation == "and" else (x or y))
            output = data["binary_output"]
            assert output >= 0
            assert (wires[output] if output < len(wires) else False) == target
        assert data["binary_size"] == len(data["binary_gates"])
        assert data["binary_ands"] == sum(op == "and" for op, _, _ in data["binary_gates"]) <= k
        sat_count += 1
        print("SAT_MODEL_PASS", stem, "all", 1 << n, "assignments and all CNF clauses")
    print("TOTAL", len(cases), "CNFs reconstructed;", sat_count, "SAT witnesses checked")


if __name__ == "__main__":
    main()
