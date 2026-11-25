import argparse
import json
import time
from pathlib import Path

from derive_subgraph import evaluate, min_cover, optimal_keep, prune, witnesses


def matching_cover(n, p, edges):
    adj = [[] for _ in range(p)]
    for a, b in edges:
        adj[a].append(b)
    mt = {}

    def aug(a, seen):
        for b in adj[a]:
            if b in seen:
                continue
            seen.add(b)
            if b not in mt or aug(mt[b], seen):
                mt[b] = a
                return True
        return False

    for a in range(p):
        aug(a, set())
    left = set(range(p)) - set(mt.values())
    right = set()
    pending = list(left)
    while pending:
        a = pending.pop()
        for b in adj[a]:
            if mt.get(b) == a or b in right:
                continue
            right.add(b)
            if b in mt and mt[b] not in left:
                left.add(mt[b])
                pending.append(mt[b])
    cover = (set(range(p)) - left) | right
    assert len(set(mt.values())) == len(mt) and all((a, b) in edges for b, a in mt.items())
    assert len(cover) == len(mt) and all(a in cover or b in cover for a, b in edges)
    return len(mt), sum(1 << v for v in cover)


def variants(n, gates, output):
    yield ("original", gates, output)
    for j, (op, a, b) in enumerate(gates):
        gs = [g[:] for g in gates]
        gs[j][0] = 1 - op
        yield (f"flip-{j}", gs, output)
        for side in (1, 2):
            for src in range(n + j):
                if gates[j][side] == src:
                    continue
                gs = [g[:] for g in gates]
                gs[j][side] = src
                yield (f"read-{j}-{side}-{src}", gs, output)
        for src in range(n + j):
            gs = [g[:] for g in gates]
            for k in range(j + 1, len(gs)):
                gs[k][1] = src if gs[k][1] == n + j else gs[k][1]
                gs[k][2] = src if gs[k][2] == n + j else gs[k][2]
            out = src if output == n + j else output
            yield (f"redirect-{j}-{src}", gs, out)


def run(graph_path, candidate_path, outdir):
    graph = json.loads(Path(graph_path).read_text())
    circuit = json.loads(Path(candidate_path).read_text())
    n, p = graph["n"], graph["p"]
    start = time.monotonic()
    counts = {"variants": 0, "quadratic_C4free": 0, "star_covered": 0, "counterexamples": 0}
    known = {}
    records = []
    for label, gates, output in variants(n, circuit["gates"], circuit["output"]):
        counts["variants"] += 1
        vals, _, cones, val, mandatory = evaluate(n, p, gates, output)
        if not val or any(val >> (1 << i) & 1 for i in range(n)):
            continue
        edges = tuple((a, b) for a in range(n) for b in range(a + 1, n)
                      if val >> ((1 << a) | (1 << b)) & 1)
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
        counts["quadratic_C4free"] += 1
        if known.get(edges, 1 << 30) <= mandatory.bit_count():
            continue
        tau, cover = matching_cover(n, p, edges)
        ws = witnesses(n, p, edges, gates, vals)
        keep, details = optimal_keep(gates, ws, cones, mandatory, len(edges))
        if keep is None:
            continue
        gs, out = prune(n, gates, output, keep)
        vals2, mixed, _, val2, _ = evaluate(n, p, gs, out)
        if mixed:
            continue
        assert val2 == target
        ws2 = witnesses(n, p, edges, gs, vals2)
        cov = 0
        for w in ws2:
            cov |= w["coverage"]
        assert cov == (1 << len(edges)) - 1
        counts["star_covered"] += 1
        known[edges] = len(gs)
        record = {"mutation": label, "edges": edges, "tau": tau, "cover_mask": cover,
                  "gates": len(gs), "bound": len(edges) + tau - 1,
                  "margin": len(gs) - (len(edges) + tau - 1), "pruning": details}
        records.append(record)
        if record["margin"] < 0:
            brute_tau, _ = min_cover(n, edges)
            assert brute_tau == tau
            counts["counterexamples"] += 1
            Path(outdir, "counterexample.json").write_text(json.dumps(
                {"graph": {"name": graph["name"] + "_mutated", "n": n, "p": p,
                           "l": n-p, "edges": edges, "tau": tau},
                 "circuit": {"gates": gs, "output": out}, "record": record}, indent=2) + "\n")
            break
    summary = {**counts, "seconds": time.monotonic() - start, "distinct_graphs": len(known),
               "minimum_margin": min((r["margin"] for r in records), default=None)}
    Path(outdir, "mutation-results.json").write_text(json.dumps(records, indent=2) + "\n")
    Path(outdir, "mutation-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("graph")
    parser.add_argument("candidate")
    parser.add_argument("outdir")
    args = parser.parse_args()
    Path(args.outdir).mkdir(parents=True, exist_ok=True)
    run(args.graph, args.candidate, args.outdir)
