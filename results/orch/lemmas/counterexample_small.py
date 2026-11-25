"""Exhaust monotone binary circuit function sets on small labelled graphs."""
from itertools import combinations
from datetime import datetime, timezone
import argparse
import json


def cases(n):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        edges = [e for i, e in enumerate(pairs) if mask >> i & 1]
        adj = {e for e in edges} | {(b, a) for a, b in edges}
        if any((a, b) in adj and (b, c) in adj and (c, a) in adj
               for a, b, c in combinations(range(n), 3)):
            continue
        if any(sum((a, c) in adj and (b, c) in adj for c in range(n)) >= 2
               for a, b in pairs):
            continue
        tt = sum(1 << x for x in range(1 << n)
                 if any(x >> a & x >> b & 1 for a, b in edges))
        yield tt, edges


def star_profile(n, edges, program):
    cones = [set() for _ in range(n)]
    vals = [sum(1 << k for k, (u, v) in enumerate(edges) if i in (u, v))
            for i in range(n)]
    ands = set()
    owned = []
    for i, (op, a, b) in enumerate(program, n):
        cones.append(cones[a] | cones[b] | ({a} if a >= n else set())
                     | ({b} if b >= n else set()))
        vals.append(vals[a] & vals[b] if op == "and" else vals[a] | vals[b])
        if op == "and":
            ands.add(i)
            own = vals[i]
            for j in cones[i] & ands:
                own &= ~vals[j]
            owned_edges = [e for k, e in enumerate(edges) if own >> k & 1]
            common = set(range(n))
            for e in owned_edges:
                common &= set(e)
            owned.append({"gate": i - n, "edges": owned_edges,
                          "star": bool(owned_edges) and bool(common)})
    return all(g["star"] for g in owned), owned


def reconstruct(state, parents, n):
    stages = []
    while parents[state] is not None:
        old, op, a, b, tt = parents[state]
        stages.append((op, a, b, tt))
        state = old
    stages.reverse()
    wire = {sum(1 << x for x in range(1 << n) if x >> i & 1): i
            for i in range(n)}
    program = []
    for op, a, b, tt in stages:
        program.append((op, wire[a], wire[b]))
        wire[tt] = n + len(program) - 1
    return program


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=4)
    parser.add_argument("--depth", type=int, default=4)
    parser.add_argument("--terminal-only", action="store_true",
                        help="Only retain newly reached targets at the last depth")
    args = parser.parse_args()
    n = args.n
    targets = dict(cases(n))
    targets.pop(0, None)
    initial = tuple(sorted(sum(1 << x for x in range(1 << n) if x >> i & 1)
                           for i in range(n)))
    parents = {initial: None}
    layer = [initial]
    found = {}
    print(json.dumps({"utc": datetime.now(timezone.utc).isoformat(), "n": n,
                      "targets": len(targets)}), flush=True)
    for depth in range(1, args.depth + 1):
        next_layer = []
        for state in layer:
            existing = set(state)
            produced = {}
            for a, b in combinations(state, 2):
                for op, tt in (("and", a & b), ("or", a | b)):
                    if args.terminal_only and depth == args.depth and (
                            tt not in targets or tt in found):
                        continue
                    if tt in existing or tt in produced:
                        continue
                    produced[tt] = (op, a, b)
            for tt, (op, a, b) in produced.items():
                new = tuple(sorted((*state, tt)))
                if new in parents:
                    continue
                parents[new] = (state, op, a, b, tt)
                next_layer.append(new)
                if tt in targets and tt not in found:
                    program = reconstruct(new, parents, n)
                    good, owned = star_profile(n, targets[tt], program)
                    found[tt] = depth
                    print(json.dumps({"edges": targets[tt], "minimum": depth,
                                      "program": program, "star": good,
                                      "owned": owned}), flush=True)
        layer = next_layer
        print(json.dumps({"depth": depth, "states": len(layer),
                          "total_states": len(parents), "found": len(found)}), flush=True)
        if len(found) == len(targets):
            break
    print(json.dumps({"unfound": [v for k, v in targets.items() if k not in found]}), flush=True)


if __name__ == "__main__":
    main()
