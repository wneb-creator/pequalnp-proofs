import argparse
import copy
import importlib.util
import json
from pathlib import Path


def normalize(model):
    result = copy.deepcopy(model)
    removed = []
    for selected in result["output"]:
        source = 26 + selected
        for j in range(selected + 1, len(result["ands"])):
            for side in ("left", "right"):
                if source in result["ands"][j][side]:
                    result["ands"][j][side].remove(source)
                    removed.append([selected, j, side])
    for selected in result["output"]:
        assert all(26 + selected not in node["left"] + node["right"]
                   for node in result["ands"][selected + 1:])
    return result, removed


def expansion_bound(model):
    return (sum(len(node["left"]) + len(node["right"]) - 1
                for node in model["ands"] if node["left"] and node["right"])
            + max(len(model["output"]) - 1, 0))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--base", required=True)
    parser.add_argument("--prefix", required=True)
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location("andcount_base", args.base)
    base = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(base)
    original = json.loads(Path(args.model).read_text())
    edges, rows = base.geometry()
    original_value = base.evaluate(original, rows)[1]
    normalized, removed = normalize(original)
    assert base.evaluate(normalized, rows)[1] == original_value
    old_circuit = base.materialize(original)
    new_circuit = base.materialize(normalized)
    assert base.ordinary_eval(new_circuit, rows) == original_value
    assert expansion_bound(normalized) <= expansion_bound(original)
    best = new_circuit if new_circuit["size"] < old_circuit["size"] else old_circuit
    prefix = Path(args.prefix)
    def save(suffix, data):
        Path(str(prefix) + suffix).write_text(json.dumps(data, indent=2) + "\n")
    save(".and-model.json", normalized)
    save(".ordinary.json", new_circuit)
    save(".best.ordinary.json", best)
    Path(str(prefix) + ".ordinary.txt").write_text("".join(f"{op} {a} {b}\n" for op, a, b in new_circuit["gates"]))
    report = {"source_memberships_removed": removed, "and_slots": len(normalized["ands"]),
              "boundary_output_unchanged": True, "original_materialized_size": old_circuit["size"],
              "normalized_materialized_size": new_circuit["size"], "best_retained_size": best["size"],
              "original_unshared_expansion_upper_bound": expansion_bound(original),
              "normalized_unshared_expansion_upper_bound": expansion_bound(normalized),
              "target_boundary_valid": original_value == (1 << 52) - 1,
              "actual_cached_size_need_not_decrease": True}
    save(".json", report)
    print(json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
