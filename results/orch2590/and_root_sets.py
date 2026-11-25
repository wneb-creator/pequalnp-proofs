from itertools import combinations

EDGES = {(min(a, b), max(a, b)) for a, b in [
    (0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
]}
NEIGHBORS = {
    v: {b if a == v else a for a, b in EDGES if v in (a, b)}
    for v in range(10)
}

survivors = []
for size in range(1, 11):
    for values in combinations(range(10), size):
        omitted = set(values)
        if any(a in omitted and b in omitted for a, b in EDGES):
            continue
        retained = set(range(10)) - omitted
        forced_singletons = set.union(*(NEIGHBORS[v] for v in omitted))
        colors = {}
        components = []
        good = True
        for start in retained:
            if start in colors:
                continue
            colors[start] = 0
            queue = [start]
            component = []
            for vertex in queue:
                component.append(vertex)
                for neighbor in NEIGHBORS[vertex] & retained:
                    if neighbor in colors:
                        if colors[neighbor] == colors[vertex]:
                            good = False
                    else:
                        colors[neighbor] = 1 - colors[vertex]
                        queue.append(neighbor)
            components.append(component)
        if not good:
            continue
        for component in components:
            for a, b in combinations(component, 2):
                if (colors[a] != colors[b]
                        and (min(a, b), max(a, b)) not in EDGES
                        and {a, b} & forced_singletons):
                    good = False
        if good:
            survivors.append(values)
            assert len(values) == 4
            assert forced_singletons == retained
            assert len(components) == 3
            assert all(len(component) == 2 for component in components)

expected = [
    (0, 2, 8, 9), (0, 3, 6, 7), (1, 3, 5, 9),
    (1, 4, 7, 8), (2, 4, 5, 6),
]
assert survivors == expected
print('All independent omitted sets checked; five maximum independent sets survive.')
for omitted in survivors:
    print(omitted)
