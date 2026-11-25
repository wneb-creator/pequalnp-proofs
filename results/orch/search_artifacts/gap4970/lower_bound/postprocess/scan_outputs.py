import argparse
import json
from pathlib import Path

from derive_subgraph import evaluate, min_cover, optimal_keep, prune, witnesses


def scan(graph_path, candidate_path, outdir):
    graph = json.loads(Path(graph_path).read_text())
    circuit = json.loads(Path(candidate_path).read_text())
    n, p = graph["n"], graph["p"]
    gates = circuit["gates"]
    vals, _, cones, _, _ = evaluate(n, p, gates, circuit["output"])
    results = []
    for output in range(n, n + len(gates)):
        val = vals[output]
        if not val or any(val >> (1 << i) & 1 for i in range(n)):
            continue
        edges = [(a, b) for a in range(n) for b in range(a + 1, n)
                 if val >> ((1 << a) | (1 << b)) & 1]
        if not edges or any(not (a < p <= b) for a, b in edges):
            continue
        adj = [set() for _ in range(n)]
        target = 0
        for a, b in edges:
            adj[a].add(b)
            adj[b].add(a)
            target |= vals[a] & vals[b]
        if target != val or any(len(adj[a] & adj[b]) > 1 for a in range(n) for b in range(a + 1, n)):
            continue
        tau, cover = min_cover(n, edges)
        ws = witnesses(n, p, edges, gates, vals)
        keep, detail = optimal_keep(gates, ws, cones, cones[output], len(edges))
        record = {"output": output, "edges": edges, "tau": tau, "bound": len(edges) + tau - 1,
                  "cover_mask": cover, "has_star_cover": keep is not None, "detail": detail}
        if keep is not None:
            gs, out = prune(n, gates, output, keep)
            vals2, mixed, _, val2, _ = evaluate(n, p, gs, out)
            assert val2 == target
            ws2 = witnesses(n, p, edges, gs, vals2)
            coverage = 0
            for w in ws2:
                coverage |= w["coverage"]
            assert coverage == (1 << len(edges)) - 1
            record.update({"pruned_gates": len(gs), "tCount": len(mixed),
                           "margin": len(gs) - record["bound"],
                           "is_counterexample": not mixed and len(gs) < record["bound"]})
            if record["is_counterexample"]:
                Path(outdir, "counterexample.json").write_text(json.dumps(
                    {"graph": {"n": n, "p": p, "l": n-p, "edges": edges, "tau": tau},
                     "circuit": {"gates": gs, "output": out}, "record": record}, indent=2) + "\n")
        results.append(record)
    Path(outdir, "all-output-results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps({"candidate": str(candidate_path), "quadratic_C4free_outputs": len(results),
                      "star_covered_outputs": sum(r["has_star_cover"] for r in results),
                      "counterexamples": sum(r.get("is_counterexample", False) for r in results),
                      "minimum_margin": min((r["margin"] for r in results if "margin" in r), default=None)}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("graph")
    parser.add_argument("candidate")
    parser.add_argument("outdir")
    args = parser.parse_args()
    Path(args.outdir).mkdir(parents=True, exist_ok=True)
    scan(args.graph, args.candidate, args.outdir)
