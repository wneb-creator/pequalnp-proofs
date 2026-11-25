import argparse
from collections import Counter
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random


def load_base(path):
    spec = importlib.util.spec_from_file_location("andcount_base", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def factor_materialize(model, seed=0, randomized=False):
    records = model["ands"]
    count = len(records)
    for j, record in enumerate(records):
        for side in ("left", "right"):
            selected = record[side]
            assert selected == sorted(set(selected))
            assert all(type(i) is int and 0 <= i < 26 + j for i in selected)
    assert model["output"] == sorted(set(model["output"]))
    assert all(type(j) is int and 0 <= j < count for j in model["output"])

    # Source symbols keep their original AND identities until lazy emission.
    # Every helper's transitive support is checked against each consumer.
    sets = [set((0, i) for i in record[side])
            for record in records for side in ("left", "right")]
    sets.append(set((0, 26 + j) for j in model["output"]))
    support = {(0, i): frozenset([i]) for i in range(26 + count)}
    helpers = []
    rng = random.Random(seed)
    while True:
        counts = Counter(pair for terms in sets
                         for pair in itertools.combinations(sorted(terms), 2))
        candidates = [(frequency, pair) for pair, frequency in counts.items()
                      if frequency >= 2]
        if not candidates:
            break
        frequency = max(x[0] for x in candidates)
        pairs = sorted(pair for f, pair in candidates if f == frequency)
        left, right = rng.choice(pairs) if randomized else pairs[0]
        helper = (1, len(helpers))
        helpers.append((left, right))
        support[helper] = support[left] | support[right]
        replacements = 0
        for terms in sets:
            if left in terms and right in terms:
                terms.remove(left)
                terms.remove(right)
                terms.add(helper)
                replacements += 1
        assert replacements == frequency

    for j in range(count):
        for side in (0, 1):
            expanded = set().union(*(support[t] for t in sets[2*j + side]))
            original = set(records[j][("left", "right")[side]])
            assert expanded == original
            assert all(i < 26 + j for i in expanded)
    expanded_output = set().union(*(support[t] for t in sets[-1]))
    assert expanded_output == {26 + j for j in model["output"]}

    gates = []
    source_cache = {i: i for i in range(26)}
    helper_cache = {}
    gate_cache = {}
    in_progress = set()

    def gate(op, left, right):
        if op == 0 and (left is None or right is None):
            return None
        if left is None:
            return right
        if right is None or left == right:
            return left
        left, right = sorted((left, right))
        key = (op, left, right)
        if key not in gate_cache:
            assert left < 26 + len(gates) and right < 26 + len(gates)
            gate_cache[key] = 26 + len(gates)
            gates.append([op, left, right])
        return gate_cache[key]

    def emit_term(term):
        kind, index = term
        if kind == 0:
            if index in source_cache:
                return source_cache[index]
            key = ("source", index)
            assert key not in in_progress
            in_progress.add(key)
            j = index - 26
            if not sets[2*j] or not sets[2*j + 1]:
                result = None
            else:
                result = gate(0, emit_or(sets[2*j]), emit_or(sets[2*j + 1]))
            source_cache[index] = result
            in_progress.remove(key)
            return result
        if index in helper_cache:
            return helper_cache[index]
        key = ("helper", index)
        assert key not in in_progress
        in_progress.add(key)
        left, right = helpers[index]
        result = gate(1, emit_term(left), emit_term(right))
        helper_cache[index] = result
        in_progress.remove(key)
        return result

    def emit_or(terms):
        values = {emit_term(term) for term in sorted(terms)}
        values.discard(None)
        values = sorted(values)
        if randomized:
            rng.shuffle(values)
        result = None
        for value in values:
            result = gate(1, result, value)
        return result

    output = emit_or(sets[-1])
    if output is None:
        return {"gates": [], "output": None, "constant_false": True, "size": 0,
                "shared_pair_helpers": len(helpers), "seed": seed}
    live = {output}
    for j in range(len(gates)-1, -1, -1):
        if 26 + j in live:
            live.update(gates[j][1:])
    rename = {i: i for i in range(26)}
    pruned = []
    for j, (op, left, right) in enumerate(gates):
        if 26 + j in live:
            rename[26 + j] = 26 + len(pruned)
            pruned.append([op, rename[left], rename[right]])
    result = {"gates": pruned, "output": rename[output], "constant_false": False,
              "size": len(pruned), "shared_pair_helpers": len(helpers), "seed": seed}
    assert not pruned or result["output"] == 26 + len(pruned) - 1
    return result


def optimize(model, base, rows, trials):
    expected = base.evaluate(model, rows)[1]
    best = base.materialize(model)
    assert base.ordinary_eval(best, rows) == expected
    summary = [{"method": "base", "size": best["size"]}]
    for trial in range(trials + 1):
        candidate = factor_materialize(model, trial, randomized=trial > 0)
        assert base.ordinary_eval(candidate, rows) == expected
        summary.append({"method": "shared_pair", "trial": trial,
                        "size": candidate["size"],
                        "helpers": candidate["shared_pair_helpers"]})
        if candidate["size"] < best["size"]:
            best = candidate
    best["ordinary_ands"] = sum(op == 0 for op, _, _ in best["gates"])
    return best, summary


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--base", required=True)
    parser.add_argument("--prefix", required=True)
    parser.add_argument("--trials", type=int, default=32)
    args = parser.parse_args()
    assert args.trials >= 0
    base = load_base(args.base)
    model_path = Path(args.model)
    model = json.loads(model_path.read_text())
    edges, rows = base.geometry()
    best, summary = optimize(model, base, rows, args.trials)
    actual = base.ordinary_eval(best, rows)
    expected = sum(1 << k for k, row in enumerate(rows)
                   if any(row >> a & 1 and row >> b & 1 for a, b in edges))
    mismatches = [rows[k] for k in range(len(rows)) if (actual ^ expected) >> k & 1]
    best.update({"boundary_mismatches": mismatches,
                 "status": "complete_boundary_valid" if not mismatches else "candidate_invalid",
                 "within_63_gate_bound": best["size"] <= 63,
                 "model_sha256": hashlib.sha256(model_path.read_bytes()).hexdigest(),
                 "method_trials": summary})
    prefix = Path(args.prefix)
    prefix.with_suffix(".json").write_text(json.dumps(best, indent=2) + "\n")
    prefix.with_suffix(".txt").write_text("".join(f"{op} {left} {right}\n"
                                                for op, left, right in best["gates"]))
    print(json.dumps({key: best[key] for key in ("size", "ordinary_ands", "status",
                                                "within_63_gate_bound", "boundary_mismatches")}, sort_keys=True))


if __name__ == "__main__":
    main()
