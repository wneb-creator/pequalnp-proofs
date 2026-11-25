import itertools
import json

D = {0, 1, 3, 9}
reps = [(7, 904), (13, 2848), (19, 708), (21, 2720),
        (25, 2656), (37, 2440), (41, 2370), (133, 808)]
lines = [{(line + d) % 13 for d in D} for line in range(13)]
points = lines[0] | lines[1]
point_mask = sum(1 << p for p in points)


def transformed_row(a, b, multiplier, translation, dual):
    if dual:
        a, b = b, a
    sign = -1 if dual else 1
    return tuple(sum(1 << i for i in range(13)
                     if mask >> ((sign * (multiplier * i + translation)) % 13) & 1)
                 for mask in (a, b))


rows = {transformed_row(a, b, m, t, d)
        for a, b in reps for m in (1, 3, 9) for t in range(13)
        for d in (False, True)}
projected = {(a & point_mask) | (b << 13) for a, b in rows}
maximal = [r for r in projected
           if not any(r != s and r & s == r for s in projected)]
assert all(not any((a >> p & 1) and (b >> line & 1)
                   for line in range(13) for p in lines[line])
           for a, b in rows)
shapes = sorted({((x & 8191).bit_count(), (x >> 13).bit_count())
                 for x in maximal})
report = {
    'points': sorted(points),
    'omitted_points': sorted(set(range(13)) - points),
    'positive_incident_pairs': sum(len(line & points) for line in lines),
    'projected_rows': len(projected),
    'undominated_projected_rows': len(maximal),
    'maximal_row_shapes': {str(shape): sum(
        ((x & 8191).bit_count(), (x >> 13).bit_count()) == shape
        for x in maximal) for shape in shapes},
    'line_neighborhood_sizes': [len(line & points) for line in lines],
    'collinear_point_triples': len({tuple(t)
        for line in lines for t in itertools.combinations(sorted(line & points), 3)}),
    'baseline_residual_gates': 7 * 4 + 6,
    'boundary_gates_including_join': 6 * 4 + 5 + 1,
}
assert report['positive_incident_pairs'] == 28
assert report['collinear_point_triples'] == 8
assert report['baseline_residual_gates'] == 34
assert report['boundary_gates_including_join'] == 30
print(json.dumps(report, indent=2))
