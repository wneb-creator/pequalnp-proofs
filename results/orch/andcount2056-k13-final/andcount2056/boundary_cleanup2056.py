import argparse
import importlib.util
import json
from pathlib import Path


def load_base(path):
    spec = importlib.util.spec_from_file_location("andcount_base", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def cleanup(circuit, base):
    edges, rows = base.geometry()
    positive = sum(1 << k for k, row in enumerate(rows)
                   if any(row >> a & 1 and row >> b & 1 for a, b in edges))
    negative = ((1 << len(rows)) - 1) ^ positive
    assert not circuit.get("constant_false", False)
    assert base.ordinary_eval(circuit, rows) == positive
    original_gates = circuit["gates"]
    output = circuit["output"]
    assert type(output) is int and 0 <= output < 26 + len(original_gates)
    profiles = [sum(((row >> i) & 1) << k for k, row in enumerate(rows))
                for i in range(26)]
    rename = {i: i for i in range(26)}
    gates = []
    changes = []

    def profile(wire):
        return 0 if wire is None else profiles[wire]

    for j, record in enumerate(original_gates):
        op, old_left, old_right = record
        assert type(op) is int and op in (0, 1)
        assert type(old_left) is int and 0 <= old_left < 26 + j
        assert type(old_right) is int and 0 <= old_right < 26 + j
        left, right = rename[old_left], rename[old_right]
        wanted = (profile(left) | profile(right)) if op else (profile(left) & profile(right))
        if not (wanted & positive):
            replacement = None
            reason = "zero-positive false substitution"
        else:
            choices = [i for i, earlier in enumerate(profiles)
                       if (wanted & positive & ~earlier) == 0
                       and (earlier & negative & ~wanted) == 0]
            if choices:
                replacement = max(choices, key=lambda i: (
                    (profiles[i] & positive).bit_count() - (profiles[i] & negative).bit_count(), -i))
                reason = "earlier row-directed dominator"
            else:
                # With no dominator, neither operand can be false or identical:
                # such a gate would equal an earlier wire or have no positives.
                assert left is not None and right is not None and left != right
                replacement = 26 + len(gates)
                gates.append([op, left, right])
                profiles.append(wanted)
                reason = None
        if reason is not None:
            actual = profile(replacement)
            assert (wanted & positive & ~actual) == 0
            assert (actual & negative & ~wanted) == 0
            changes.append({"old_gate": j, "replacement_during_construction": replacement,
                            "reason": reason})
        rename[26 + j] = replacement

    output = rename[output]
    assert output is not None and profile(output) == positive
    live = {output}
    for j in range(len(gates)-1, -1, -1):
        if 26 + j in live:
            live.update(gates[j][1:])
    final_rename = {i: i for i in range(26)}
    pruned = []
    for j, (op, left, right) in enumerate(gates):
        if 26 + j in live:
            final_rename[26 + j] = 26 + len(pruned)
            pruned.append([op, final_rename[left], final_rename[right]])
    result = {"gates": pruned, "output": final_rename[output], "constant_false": False,
              "size": len(pruned), "ordinary_ands": sum(op == 0 for op, _, _ in pruned),
              "original_size": len(original_gates), "replacements": changes,
              "status": "complete_boundary_valid", "within_63_gate_bound": len(pruned) <= 63}
    assert result["size"] <= len(original_gates)
    assert not pruned or result["output"] == 26 + len(pruned) - 1
    assert base.ordinary_eval(result, rows) == positive
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--circuit", required=True)
    parser.add_argument("--base", required=True)
    parser.add_argument("--prefix", required=True)
    args = parser.parse_args()
    base = load_base(args.base)
    result = cleanup(json.loads(Path(args.circuit).read_text()), base)
    prefix = Path(args.prefix)
    prefix.with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    prefix.with_suffix(".txt").write_text("".join(f"{op} {a} {b}\n" for op, a, b in result["gates"]))
    print(json.dumps({key: result[key] for key in ("original_size", "size", "ordinary_ands",
                                                 "status", "within_63_gate_bound")}, sort_keys=True))


if __name__ == "__main__":
    main()
