import itertools
import json
import pathlib

HERE = pathlib.Path(__file__).resolve().parent
cases = json.loads((HERE/'six-owner-gadgets.json').read_text())
edges = {tuple(e) for e in cases[0]['edges']}
columns = {frozenset(p for p, l in edges if l == line): line for line in range(6, 17)}
automorphisms = []
for point_perm in itertools.permutations(range(6)):
    line_perm = []
    for line in range(6, 17):
        neighbors = frozenset(point_perm[p] for p, l in edges if l == line)
        if neighbors not in columns:
            break
        line_perm.append(columns[neighbors])
    else:
        automorphisms.append(list(point_perm)+line_perm)
assert len(automorphisms) == 72


def support(feature):
    return sum(1 << i for i in feature['raw_indices'])


def transform(mask, perm):
    return sum(1 << perm[i] for i in range(17) if mask >> i & 1)


keys = [tuple(sorted(support(f) for f in c['features'])) for c in cases]
equivalents, maps = {}, []
for source, case in enumerate(cases):
    for target in range(source+1):
        target_lookup = {support(f): 17+i for i, f in enumerate(cases[target]['features'])}
        for perm in automorphisms:
            transformed = [transform(support(f), perm) for f in case['features']]
            if tuple(sorted(transformed)) == keys[target]:
                maps.append(dict(case=source, representative=target,
                                 input_permutation=perm+[target_lookup[m] for m in transformed]))
                equivalents.setdefault(target, []).append(source)
                break
        else:
            continue
        break

triples = sorted(mask for mask in keys[0] if mask.bit_count() == 3)
hub = next(mask for mask in keys[0] if mask.bit_count() == 2 and
           all(mask & triple == 0 for triple in triples))
assert len(triples) == 6
options = []
for mask in triples:
    vertices = [i for i in range(17) if mask >> i & 1]
    options.append([sum(1 << i for i in pair) for pair in itertools.combinations(vertices, 2)])
all_patterns = {tuple(sorted([hub]+triples+list(pairs))) for pairs in itertools.product(*options)}
assert len(all_patterns) == 729
unseen = all_patterns.copy()
all_orbits = []
while unseen:
    representative = min(unseen)
    orbit = {tuple(sorted(transform(mask, perm) for mask in representative)) for perm in automorphisms}
    assert orbit <= all_patterns
    unseen.difference_update(orbit)
    included = [i for i, key in enumerate(keys) if key in orbit]
    all_orbits.append(dict(size=len(orbit), representative_feature_masks=list(representative),
                           supplied_cases=included))
report = dict(group_order=72, raw_input_permutations=automorphisms,
              supplied_prefix_orbits=equivalents, case_to_representative=maps,
              total_prefix_patterns=729, all_prefix_orbits=all_orbits)
(HERE/'six-prefix-orbits.json').write_text(json.dumps(report))
print(dict(group_order=72, supplied_orbits=equivalents, total_orbits=len(all_orbits),
           orbit_sizes=[o['size'] for o in all_orbits],
           represented_orbits=sum(bool(o['supplied_cases']) for o in all_orbits)))
