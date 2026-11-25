import argparse
import hashlib
import json
from functools import lru_cache
from pathlib import Path


@lru_cache(maxsize=None)
def columns(n):
    return tuple(sum(1 << row for row in range(1 << n) if row >> i & 1) for i in range(n))


def evaluate(n, p, gates, output):
    vals = list(columns(n))
    reach = [1 << i for i in range(n)]
    cones = [0] * n
    mixed = []
    left = (1 << p) - 1
    right = ((1 << n) - 1) ^ left
    for j, (op, a, b) in enumerate(gates):
        assert op in (0, 1) and 0 <= a < n + j and 0 <= b < n + j
        vals.append((vals[a] | vals[b]) if op else (vals[a] & vals[b]))
        reach.append((reach[a] | reach[b]) if op else 0)
        cones.append(cones[a] | cones[b] | (1 << j))
        if op and reach[-1] & left and reach[-1] & right:
            mixed.append(j)
    outval = vals[output] if 0 <= output < len(vals) else 0
    outcone = cones[output] if 0 <= output < len(vals) else 0
    return vals, mixed, cones, outval, outcone


def min_cover(n, edges):
    for k in range(n + 1):
        for mask in range(1 << n):
            if mask.bit_count() == k and all(mask >> a & 1 or mask >> b & 1 for a, b in edges):
                return k, mask
    raise AssertionError("cover enumeration failed")


def witnesses(n, p, edges, gates, vals):
    adj = [0] * n
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    result = []
    for j, (op, _, _) in enumerate(gates):
        if not op:
            continue
        val = vals[n + j]
        support = sum(1 << i for i in range(n) if val >> (1 << i) & 1)
        if support.bit_count() < 2:
            continue
        pure = 0
        for i in range(n):
            if support >> i & 1:
                pure |= vals[i]
        if pure != val:
            continue
        for c in range(n):
            if support & ~adj[c] == 0:
                cov = sum(1 << k for k, (a, b) in enumerate(edges)
                          if (a == c and support >> b & 1) or (b == c and support >> a & 1))
                result.append({"gate": j, "center": c, "support_mask": support, "coverage": cov})
    return result


def optimal_keep(gates, witnesses_, cones, mandatory, edge_count):
    target = (1 << edge_count) - 1
    ws = [(w["coverage"], cones[len(cones) - len(gates) + w["gate"]]) for w in witnesses_]

    def covered(keep):
        result = 0
        for w in witnesses_:
            if keep >> w["gate"] & 1:
                result |= w["coverage"]
        return result

    all_cov = covered((1 << len(gates)) - 1)
    if all_cov != target:
        return None, {"missing_edge_indices": [k for k in range(edge_count) if not (all_cov >> k & 1)]}
    best = (1 << len(gates)) - 1
    visits = 0
    seen = set()

    def search(keep):
        nonlocal best, visits
        visits += 1
        if keep in seen:
            return
        seen.add(keep)
        cov = covered(keep)
        if cov == target:
            if keep.bit_count() < best.bit_count():
                best = keep
            return
        if keep.bit_count() >= best.bit_count():
            return
        remaining = [k for k in range(edge_count) if not (cov >> k & 1)]
        choices = [[keep | cone for cm, cone in ws if cm >> k & 1] for k in remaining]
        children = min(choices, key=lambda xs: len(set(xs)))
        for child in sorted(set(children), key=int.bit_count):
            search(child)

    search(mandatory)
    return best, {"search_states": visits, "distinct_states": len(seen)}


def prune(n, gates, output, keep):
    ren = {i: i for i in range(n)}
    result = []
    for j, (op, a, b) in enumerate(gates):
        if keep >> j & 1:
            assert a in ren and b in ren
            ren[n + j] = n + len(result)
            result.append([op, ren[a], ren[b]])
    assert output in ren
    return result, ren[output]


def process(graph_path, candidate_path, output_dir):
    graph = json.loads(Path(graph_path).read_text())
    raw = Path(candidate_path).read_bytes()
    candidate = json.loads(raw)
    Path(output_dir, "input.circuit.json").write_bytes(raw)
    Path(output_dir, "input.graph.json").write_text(json.dumps(graph, indent=2) + "\n")
    n, p = graph["n"], graph["p"]
    gates, output = candidate["gates"], candidate["output"]
    vals, mixed, cones, outval, mandatory = evaluate(n, p, gates, output)
    accepted = [(a, b) for a in range(n) for b in range(a + 1, n)
                if outval >> ((1 << a) | (1 << b)) & 1]
    singleton_rows = [i for i in range(n) if outval >> (1 << i) & 1]
    bipartite = all(a < p <= b for a, b in accepted)
    target = 0
    for a, b in accepted:
        target |= vals[a] & vals[b]
    diff = outval ^ target
    adj = [set() for _ in range(n)]
    for a, b in accepted:
        adj[a].add(b)
        adj[b].add(a)
    c4free = all(len(adj[a] & adj[b]) <= 1 for a in range(n) for b in range(a + 1, n))
    original_edges = {tuple(e) for e in graph["edges"]}
    result = {
        "source": str(candidate_path), "sha256": hashlib.sha256(raw).hexdigest(),
        "original_graph": graph["name"], "n": n, "p": p, "original_gates": len(gates),
        "derived_edges": accepted, "removed_edges": sorted(original_edges - set(accepted)),
        "extra_pairs": sorted(set(accepted) - original_edges), "bipartite": bipartite,
        "c4free": c4free, "singleton_true_inputs": singleton_rows,
        "full_rows_checked": 1 << n, "quadratic_wrong_rows": diff.bit_count(),
        "first_wrong_rows": [r for r in range(1 << n) if diff >> r & 1][:20],
        "tCount": len(mixed), "output_cone_size": mandatory.bit_count(),
    }
    if bipartite and c4free and not singleton_rows and diff == 0 and accepted:
        tau, cover = min_cover(n, accepted)
        ws = witnesses(n, p, accepted, gates, vals)
        keep, details = optimal_keep(gates, ws, cones, mandatory, len(accepted))
        result.update({"tau": tau, "minimum_cover_mask": cover,
                       "posted_bound": len(accepted) + tau - 1,
                       "valid_witnesses": ws, "pruning": details})
        if keep is not None:
            new_gates, new_output = prune(n, gates, output, keep)
            vals2, mixed2, _, out2, _ = evaluate(n, p, new_gates, new_output)
            ws2 = witnesses(n, p, accepted, new_gates, vals2)
            cov2 = 0
            for w in ws2:
                cov2 |= w["coverage"]
            assert out2 == target and cov2 == (1 << len(accepted)) - 1
            result.update({"pruned_gates": len(new_gates), "pruned_tCount": len(mixed2),
                           "kept_gate_mask": keep,
                           "is_counterexample": len(mixed2) == 0 and len(new_gates) < len(accepted) + tau - 1})
            Path(output_dir, "pruned.circuit.json").write_text(json.dumps(
                {"gates": new_gates, "output": new_output}, indent=2) + "\n")
            Path(output_dir, "derived.graph.json").write_text(json.dumps(
                {"name": graph["name"] + "_derived", "n": n, "p": p, "l": n-p,
                 "edges": accepted, "tau": tau}, indent=2) + "\n")
    Path(output_dir, "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("graph")
    parser.add_argument("candidate")
    parser.add_argument("output_dir")
    args = parser.parse_args()
    Path(args.output_dir).mkdir(parents=True, exist_ok=True)
    process(args.graph, args.candidate, args.output_dir)
