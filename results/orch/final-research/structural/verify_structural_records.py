#!/usr/bin/env python3
"""Reproduce the tool-inline structural checks from the frozen JSON records.

These are exhaustive finite computational checks, not Lean certificates and not
counterexamples to L-meta-2602. No network access or external solver is used.
"""

import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def inputs(n):
    return [sum(1 << row for row in range(1 << n) if row >> i & 1)
            for i in range(n)]


def evaluate(n, gates, replace=None, clamp=None):
    values = inputs(n)
    for j, (op, a, b) in enumerate(gates):
        assert op in ("and", "or")
        assert a != b and a < n + j and b < n + j
        value = values[a] & values[b] if op == "and" else values[a] | values[b]
        if replace is not None and replace[0] == j:
            value = values[(a, b)[replace[1]]]
        if clamp == j:
            value = 0
        values.append(value)
    return values


def derivative(n, gates, output, base, seed):
    values = [i == base for i in range(n)]
    derivs = [i == seed for i in range(n)]
    for op, a, b in gates:
        values.append(values[a] and values[b] if op == "and"
                      else values[a] or values[b])
        derivs.append((values[a] and derivs[b]) or (derivs[a] and values[b])
                      if op == "and" else derivs[a] or derivs[b])
    return derivs[output]


def target(n, edges):
    return sum(1 << row for row in range(1 << n)
               if any(row >> a & 1 and row >> b & 1 for a, b in edges))


def edge_profile(function, edges):
    return sum(1 << i for i, (a, b) in enumerate(edges)
               if function >> ((1 << a) | (1 << b)) & 1)


def closure_measure(n, gates, count, function, edges, constants=True):
    full = (1 << (1 << n)) - 1
    atoms = evaluate(n, gates[:count])
    closure = {0, full} if constants else set()
    for atom in atoms:
        old = tuple(closure)
        closure.add(atom)
        closure.update(member & atom for member in old)
    clean = {edge_profile(member, edges) for member in closure
             if member & (~function & full) == 0}
    bound = 1 << len(edges)
    dp = [bound + 1] * bound
    dp[0] = 0
    for state in range(bound):
        for member in clean:
            dp[state | member] = min(dp[state | member], dp[state] + 1)
    return {"closure_size": len(closure), "clean_profiles": sorted(clean),
            "tau": dp[-1]}


def check_branch_record():
    record = json.loads((HERE / "tau-branch-irredundant-counterexample.json").read_text())
    independent = json.loads((HERE / "tau-branch-independent-check.json").read_text())
    n = 6
    gates, edges, output = record["gates"], record["edges"], record["output"]
    function = target(n, edges)
    values = evaluate(n, gates)
    assert values[output] == function
    prefix = record["prefix_gate_count"]
    measures = [closure_measure(n, gates, count, function, edges)
                for count in (prefix, prefix + 1)]
    assert measures == [record["before"], record["after_one_OR"]]
    assert measures == independent["closure_measures_with_constants"]
    strict = [closure_measure(n, gates, count, function, edges, False)
              for count in (prefix, prefix + 1)]
    assert strict == independent["closure_measures_without_constants"]
    losses = [edge_profile(function & ~evaluate(n, gates, clamp=j)[output], edges)
              for j in range(len(gates))]
    assert all(losses)
    assert losses == record["clamping_loses_edge_profiles"]
    assert losses == independent["clamping_edge_losses"]
    branches = [{"gate": j, "retain": side,
                 "changes_function": evaluate(n, gates, replace=(j, side))[output] != function}
                for j, gate in enumerate(gates) if gate[0] == "or" for side in (0, 1)]
    assert all(test["changes_function"] for test in branches)
    assert branches == record["every_OR_branch_is_globally_essential"]
    derivs = [[derivative(n, gates, output, a, b), derivative(n, gates, output, b, a)]
              for a, b in edges]
    assert not any(any(pair) for pair in derivs)
    assert derivs == record["marked_derivatives"] == independent["derivatives"]
    assert [edge_profile(value, edges) for value in values[n:]] == record["gate_edge_profiles"]
    return {"verdict": "PASS", "truth_rows": 64, "proper_gates": len(gates),
            "with_constants": measures, "without_constants": strict,
            "clamping_edge_losses": losses, "OR_branch_checks": branches,
            "derivatives": derivs}


def check_copy_record():
    source = json.loads((HERE / "tau-drop-counterexample.json").read_text())
    record = json.loads((HERE / "tau-copy-normalization.json").read_text())
    n = 10
    gates = [list(gate) for gate in source["gates"]]
    output = source["output"]
    function = evaluate(n, gates)[output]
    changes = []
    while True:
        changed = False
        for j, (op, a, b) in enumerate(gates):
            if op != "or":
                continue
            for child in (a, b):
                if child < n:
                    continue
                replacement = gates[child - n]
                if replacement == gates[j]:
                    continue
                trial = gates.copy()
                trial[j] = replacement
                if evaluate(n, trial)[output] != function:
                    continue
                assert not derivative(n, trial, output, 2, 3)
                assert not derivative(n, trial, output, 3, 2)
                changes.append({"gate": j, "old": gates[j],
                                "retained_child": child, "new": replacement})
                gates = trial
                changed = True
                break
            if changed:
                break
        if not changed:
            break
    assert gates == record["gates"] and changes == record["changes"]
    edges = [(2 * i, 2 * i + 1) for i in range(5)]
    assert function == target(n, edges)
    history = []
    for count in range(len(gates) + 1):
        measure = closure_measure(n, gates, count, function, edges)
        history.append({"prefix_gates": count, "tau": measure["tau"],
                        "clean_profiles": measure["clean_profiles"]})
    assert history == record["tau_history"]
    before = sum(gate[0] == "or" for gate in source["gates"])
    after = sum(gate[0] == "or" for gate in gates)
    assert before == record["or_before"] and after == record["or_after"]
    return {"verdict": "PASS", "truth_rows": 1024, "changes": changes,
            "or_before": before, "or_after": after, "tau_history": history,
            "both_marked_derivatives_zero": True}


if __name__ == "__main__":
    print(json.dumps({"branch_irredundant": check_branch_record(),
                      "copy_normalization": check_copy_record()}, indent=2))
