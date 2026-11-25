import argparse
import json
from pathlib import Path

from derive_subgraph import process
from local_subgraph_probe import run
from scan_outputs import scan


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("graph")
    parser.add_argument("outdir")
    parser.add_argument("candidates", nargs="+")
    args = parser.parse_args()
    base = Path(args.outdir)
    base.mkdir(parents=True, exist_ok=True)
    summaries = []
    for path in args.candidates:
        out = base / Path(path).stem
        out.mkdir(parents=True, exist_ok=True)
        process(args.graph, path, out)
        scan(args.graph, out / "input.circuit.json", out)
        run(args.graph, out / "input.circuit.json", out)
        result = json.loads((out / "result.json").read_text())
        mutations = json.loads((out / "mutation-summary.json").read_text())
        outputs = json.loads((out / "all-output-results.json").read_text())
        summaries.append({"candidate": str(path), "wrong_rows": result["quadratic_wrong_rows"],
                          "derived_edges": len(result["derived_edges"]),
                          "tau": result.get("tau"), "pruned_gates": result.get("pruned_gates"),
                          "bound": result.get("posted_bound"),
                          "outputs_checked": len(outputs), "mutations": mutations,
                          "counterexample_found": bool(result.get("is_counterexample")) or
                              any(o.get("is_counterexample", False) for o in outputs) or
                              bool(mutations["counterexamples"])})
    (base / "summary.json").write_text(json.dumps(summaries, indent=2) + "\n")
