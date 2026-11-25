#!/usr/bin/env python3
"""Test a proposed clean-cover lower-bound potential on bounded samples."""
import argparse
import json
import random
import time
from pathlib import Path


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--graphs", type=Path, required=True)
    p.add_argument("--vertices", type=int, required=True)
    p.add_argument("--seconds", type=float, default=40)
    p.add_argument("--seed", type=int, default=2602)
    args = p.parse_args()
    graphs = json.loads(args.graphs.read_text())
    n = args.vertices
    rng = random.Random(args.seed)
    all_truth = (1 << (1 << n)) - 1
    inputs = [sum(1 << x for x in range(1 << n) if (x >> i) & 1) for i in range(n)]
    monomials = {all_truth}
    for x in inputs:
        monomials.update([a & x for a in list(monomials)])

    targets = []
    for graph in graphs:
        edges = graph["edges"]
        edge_inputs = [(1 << a) | (1 << b) for a, b in edges]
        f = sum(1 << x for x in range(1 << n)
                if any((x & e) == e for e in edge_inputs))
        targets.append((edges, edge_inputs, all_truth ^ f))

    def cover(family, target):
        edges, edge_inputs, forbidden = target
        profiles = set()
        for a in family:
            if a & forbidden:
                continue
            profile = sum(1 << i for i, e in enumerate(edge_inputs) if (a >> e) & 1)
            if profile:
                profiles.add(profile)
        # Remove a profile if another available clean function covers more edges.
        profiles = [a for a in profiles if not any(a != b and (a | b) == b for b in profiles)]
        full = (1 << len(edges)) - 1
        dp = [len(edges) + 1] * (full + 1)
        dp[0] = 0
        for mask in range(full + 1):
            for profile in profiles:
                joined = mask | profile
                dp[joined] = min(dp[joined], dp[mask] + 1)
        return dp[full], profiles

    started = time.monotonic()
    steps = 0
    trials = 0
    while time.monotonic() - started < args.seconds:
        target_index = rng.randrange(len(targets))
        target = targets[target_index]
        family = set(monomials)
        old_cover, _ = cover(family, target)
        gates = []
        for depth in range(6):
            vals = tuple(family)
            chosen = None
            for _ in range(20):
                a, b = rng.sample(vals, 2)
                q = a | b
                if q not in family:
                    chosen = a, b, q
                    break
            if chosen is None:
                break
            a, b, q = chosen
            old_family = family
            family = old_family | {h & q for h in old_family}
            new_cover, profiles = cover(family, target)
            gates.append([a, b])
            steps += 1
            if old_cover > new_cover + 1:
                print(json.dumps({"counterexample": True, "vertices": n,
                                  "graph": graphs[target_index], "or_gates_truth_masks": gates,
                                  "old_cover": old_cover, "new_cover": new_cover,
                                  "old_family": sorted(old_family), "new_profiles": profiles,
                                  "steps": steps, "seconds": time.monotonic() - started}, indent=2))
                return
            old_cover = new_cover
            if old_cover == 1:
                break
        trials += 1
    print(json.dumps({"counterexample": False, "vertices": n, "graphs": len(graphs),
                      "trials": trials, "steps": steps,
                      "seconds": time.monotonic() - started, "seed": args.seed}))


if __name__ == "__main__":
    main()
