#!/usr/bin/env python3
"""Exhaustively validate first-pair Fano automorphism orbits (no solver)."""
import hashlib
import itertools
import json
from pathlib import Path

lines = [frozenset(p for p in range(7) if (p-l) % 7 in (0, 1, 3))
         for l in range(7)]
line_index = {x: i for i, x in enumerate(lines)}
edges = {tuple(sorted((p, 7+l))) for l in range(7) for p in lines[l]}
autos = set()
for pperm in itertools.permutations(range(7)):
    images = [frozenset(pperm[p] for p in line) for line in lines]
    if all(image in line_index for image in images):
        autos.add(tuple(pperm) + tuple(7+line_index[image] for image in images))
assert len(autos) == 168
duality = tuple(7+(-p) % 7 for p in range(7)) + tuple((-l) % 7 for l in range(7))
autos |= {tuple(duality[g[v]] for v in range(14)) for g in tuple(autos)}
assert len(autos) == 336
pairs = set(itertools.combinations(range(14), 2))
for g in autos:
    assert len(set(g)) == 14
    assert {tuple(sorted((g[a], g[b]))) for a, b in edges} == edges
orbits = {}
for a, b in [(0, 1), (0, 7), (0, 9)]:
    orbit = {tuple(sorted((g[a], g[b]))) for g in autos}
    orbits[f"{a},{b}"] = sorted(orbit)
assert set().union(*(set(xs) for xs in orbits.values())) == pairs
assert sum(map(len, orbits.values())) == len(pairs)
assert [len(xs) for xs in orbits.values()] == [42, 21, 28]
record = {"automorphisms": len(autos), "unordered_input_pairs": len(pairs),
          "orbits": orbits,
          "all_permutations_checked": True,
          "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
print(json.dumps(record, indent=2))
