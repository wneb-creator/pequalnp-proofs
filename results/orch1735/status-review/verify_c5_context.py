#!/usr/bin/env python3
"""Exhaustive five-variable diagnostic; no claim of global minimality."""
import json
from pathlib import Path


def evaluate(n, gates, assignment, replacement=None):
    values = [bool(assignment >> i & 1) for i in range(n)]
    for j, (operation, left, right) in enumerate(gates):
        assert 0 <= left < n + j and 0 <= right < n + j
        assert operation in {"and", "or"}
        value = (values[left] and values[right]) if operation == "and" else (
            values[left] or values[right]
        )
        if replacement is not None and replacement[0] == j:
            value = values[replacement[1]]
        values.append(value)
    return values


def main():
    data = json.loads(Path(__file__).with_name("c5-context-essential12.json").read_text())
    n, gates = data["n"], data["gates"]
    edges = {frozenset(edge) for edge in data["graph_edges"]}
    rows = range(1 << n)

    def graph(assignment):
        return any(all(assignment >> v & 1 for v in edge) for edge in edges)

    assert n == 5 and len(gates) == 12 and len(edges) == 5
    assert all(evaluate(n, gates, x)[-1] == graph(x) for x in rows)
    clean = {
        j for j, (op, _, _) in enumerate(gates)
        if op == "and" and all(
            not evaluate(n, gates, x)[n + j] or graph(x) for x in rows
        )
    }
    assert clean == {11}

    ancestors = [set() for _ in range(n)]
    raw_support = [{v} for v in range(n)]
    for j, (op, a, b) in enumerate(gates):
        ancestors.append(ancestors[a] | ancestors[b] | {j})
        raw_support.append(raw_support[a] | raw_support[b] if op == "or" else set())
    for j, (op, a, b) in enumerate(gates):
        if op == "and":
            assert not (clean & (ancestors[a] | ancestors[b]))
    stars = set()
    for j in clean:
        _, a, b = gates[j]
        stars.update(frozenset((u, v)) for u in raw_support[a] for v in raw_support[b])
    assert edges - stars == edges

    replacements_checked = 0
    for j in range(len(gates)):
        for source in range(n + j):
            assert any(evaluate(n, gates, x, (j, source))[-1] != graph(x) for x in rows)
            replacements_checked += 1

    # Three ordinary stars, covering each graph edge once; gives a strict upper bound.
    upper = [
        ["or", 1, 4], ["and", 0, 5], ["and", 1, 2],
        ["or", 2, 4], ["and", 3, 8], ["or", 6, 7], ["or", 9, 10],
    ]
    assert len(upper) == 7
    assert all(evaluate(n, upper, x)[-1] == graph(x) for x in rows)
    print(f"PASS: 32 truth rows; TopForm; Ustar=5; {replacements_checked} earlier-wire replacements fail.")
    print("PASS: explicit seven-gate circuit computes the same graph; twelve-gate witness is NOT least.")


if __name__ == "__main__":
    main()
