#!/usr/bin/env python3
"""Exhaustive finite graph census; no claim about arbitrary circuits."""
import collections
import datetime
import itertools
import json
from pathlib import Path

EDGES = [(0, 8), (0, 10), (1, 7), (1, 13), (2, 8), (2, 12),
         (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11),
         (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]


def residual(vertices):
    selected = set(vertices)
    return [i for i, (u, v) in enumerate(EDGES)
            if u not in selected and v not in selected]


def record(vertices):
    un = residual(vertices)
    degrees = collections.Counter(v for i in un for v in EDGES[i])
    return dict(vertices=list(vertices), uncovered=un,
                degree_sequence=sorted(degrees.values(), reverse=True),
                star_center=[v for v, d in degrees.items() if d == len(un)])


def automorphisms():
    """Enumerate all maps of the unique bipartition and reconstruct the rest."""
    adjacency = {v: {w if u == v else u for u, w in EDGES if u == v or w == v}
                 for v in range(14)}
    answer = []
    for destination in [tuple(range(7)), tuple(range(7, 14))]:
        opposite = set(range(14)) - set(destination)
        inverse = {frozenset(adjacency[v]): v for v in opposite}
        assert len(inverse) == 7
        for perm in itertools.permutations(destination):
            right = [inverse.get(frozenset(perm[u] for u in adjacency[v]))
                     for v in range(7, 14)]
            if None not in right:
                g = tuple(perm) + tuple(right)
                assert {tuple(sorted((g[u], g[v]))) for u, v in EDGES} == set(EDGES)
                answer.append(g)
    return sorted(answer)


def main():
    table = {k: [record(s) for s in itertools.combinations(range(14), k)]
             for k in range(8)}
    profile = []
    for k, rows in table.items():
        minimum = min(len(r['uncovered']) for r in rows)
        profile.append(dict(k=k, minimum=minimum,
                            count=sum(len(r['uncovered']) == minimum for r in rows)))
    six_two = [r for r in table[6] if len(r['uncovered']) == 2]
    six_three = [r for r in table[6] if len(r['uncovered']) == 3]
    group = automorphisms()
    remaining = {tuple(r['vertices']): r for r in six_three}
    orbits = []
    while remaining:
        s = min(remaining)
        orbit = sorted({tuple(sorted(g[i] for i in s)) for g in group})
        row = remaining[s]
        orbits.append(dict(representative=s, size=len(orbit),
                           residual_degrees=row['degree_sequence'],
                           uncovered=row['uncovered'], sets=orbit))
        for t in orbit:
            del remaining[t]
    data = dict(at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                edges=EDGES, profile=profile, six_two=six_two, six_three=six_three,
                automorphisms=group, six_three_orbits=orbits)
    output = Path(__file__).with_name('graph-profile.json')
    output.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps(dict(profile=profile, automorphisms=len(group),
                          six_three=len(six_three), six_three_orbits=len(orbits),
                          residual_types=dict(collections.Counter(
                              str(r['degree_sequence']) for r in six_three))), indent=2))


if __name__ == '__main__':
    main()
