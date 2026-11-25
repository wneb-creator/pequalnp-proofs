import argparse
import itertools
import json
from pathlib import Path


VARIABLES = [0, 3, 5, 6, 7, 8, 9, 10, 11, 12]
EDGES = [(0, 4), (0, 5), (0, 7), (1, 4), (1, 8), (1, 9),
         (2, 6), (2, 7), (2, 9), (3, 5), (3, 6), (3, 8)]
MATCHING_SUMS = [(4, 6), (5, 9), (7, 8)]
HEAWOOD = [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13),
           (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12),
           (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
           (6, 8), (6, 9), (6, 11)]


def graph_value(values, edges):
    return any(values[a] and values[b] for a, b in edges)


def cut_values(mask):
    values = [bool(mask & (1 << i)) for i in range(10)]
    values.extend(values[a] or values[b] for a, b in MATCHING_SUMS)
    return values


def evaluate(initial, gates):
    values = list(initial)
    for op, a, b in gates:
        assert op in (0, 1) and 0 <= a < len(values) and 0 <= b < len(values)
        values.append((values[a] or values[b]) if op else (values[a] and values[b]))
    return values


def star_cone(missing=None):
    gates, terms = [], []
    for left in range(4):
        neighbors = [b for a, b in EDGES if a == left and (a, b) != missing]
        wire = neighbors[0]
        for other in neighbors[1:]:
            gates.append([1, wire, other])
            wire = 12 + len(gates)
        gates.append([0, left, wire])
        terms.append(12 + len(gates))
    output = terms[0]
    for term in terms[1:]:
        gates.append([1, output, term])
        output = 12 + len(gates)
    return gates, output


def fixed_stars():
    gates, sums, terms = [], [], []
    for left, a, b in ((1, 7, 9), (2, 8, 12), (4, 10, 11)):
        gates.append([1, a, b])
        sums.append(13 + len(gates))
        gates.append([1, 13, sums[-1]])
        gates.append([0, left, 13 + len(gates)])
        terms.append(13 + len(gates))
    gates.append([1, terms[0], terms[1]])
    gates.append([1, 13 + len(gates), terms[2]])
    assert len(gates) == 11
    return gates, sums, 24


def embed(cone, output):
    gates, sums, fixed_output = fixed_stars()
    mapping = VARIABLES + sums
    for op, a, b in cone:
        gates.append([op, mapping[a], mapping[b]])
        mapping.append(13 + len(gates))
    gates.append([1, fixed_output, mapping[output]])
    return gates


def automorphisms():
    endpoints = {r: tuple(a for a, b in EDGES if b == r) for r in range(4, 10)}
    right_of = {tuple(sorted(pair)): r for r, pair in endpoints.items()}
    sum_of = {tuple(sorted(pair)): 10 + i for i, pair in enumerate(MATCHING_SUMS)}
    result = []
    for vertices in itertools.permutations(range(4)):
        perm = list(vertices)
        perm.extend(right_of[tuple(sorted(vertices[a] for a in endpoints[r]))]
                    for r in range(4, 10))
        perm.extend(sum_of[tuple(sorted((perm[a], perm[b])))] for a, b in MATCHING_SUMS)
        assert sorted(perm) == list(range(13))
        for mask in range(1 << 10):
            image_mask = sum(1 << perm[v] for v in range(10) if mask & (1 << v))
            old, new = cut_values(mask), cut_values(image_mask)
            assert all(old[v] == new[perm[v]] for v in range(13))
            assert graph_value(old, EDGES) == graph_value(new, EDGES)
        result.append(perm)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', required=True)
    args = parser.parse_args()
    output_dir = Path(args.output_dir)
    positives = sorted((1 << a) | (1 << b) for a, b in EDGES)
    negatives = []
    for mask in range(1 << 10):
        values = cut_values(mask)
        if graph_value(values, EDGES):
            continue
        if all(graph_value(cut_values(mask | (1 << i)), EDGES)
               for i in range(10) if not mask & (1 << i)):
            negatives.append(mask)
    rows = [dict(mask=m, value=int(m in positives), cuts=list(map(int, cut_values(m))))
            for m in sorted(positives + negatives)]
    for mask in range(1 << 10):
        if graph_value(cut_values(mask), EDGES):
            assert any(p & mask == p for p in positives)
        else:
            assert any(mask & n == mask for n in negatives)
    baseline, baseline_output = star_cone()
    missing = (0, 4)
    seed, seed_output = star_cone(missing)
    assert len(baseline) == 15 and len(seed) == 14
    seed_errors = 0
    for mask in range(1 << 10):
        initial = cut_values(mask)
        assert evaluate(initial, baseline)[baseline_output] == graph_value(initial, EDGES)
        value = evaluate(initial, seed)[seed_output]
        assert value == graph_value(initial, [e for e in EDGES if e != missing])
        seed_errors += value != graph_value(initial, EDGES)
    full = embed(seed, seed_output)
    full_baseline = embed(baseline, baseline_output)
    assert len(full) == 26 and len(full_baseline) == 27
    missing_original = (VARIABLES[missing[0]], VARIABLES[missing[1]])
    full_errors = 0
    for mask in range(1 << 14):
        initial = [bool(mask & (1 << i)) for i in range(14)]
        target = graph_value(initial, HEAWOOD)
        assert evaluate(initial, full_baseline)[-1] == target
        value = evaluate(initial, full)[-1]
        assert value == graph_value(initial, [e for e in HEAWOOD if e != missing_original])
        full_errors += value != target
    data = dict(real_inputs=10, cut_inputs=13, cone_gate_budget=14,
                original_variables=VARIABLES, edges=EDGES,
                free_or_sums=MATCHING_SUMS, positive_rows=positives,
                negative_rows=negatives, rows=rows,
                fixed_gates=fixed_stars()[0], fixed_sum_wires=fixed_stars()[1],
                fixed_output=24, checked_residual_assignments=1024)
    (output_dir / 'matching-cut-cone-rows.json').write_text(json.dumps(data, indent=2) + '\n')
    autos = automorphisms()
    representatives = sorted({min(tuple(sorted((p[a], p[b]))) for p in autos)
                              for a in range(13) for b in range(a + 1, 13)})
    all_representatives = sorted({min(tuple(sorted((p[a], p[b]))) for p in autos)
                                  for a in range(13) for b in range(a, 13)})
    (output_dir / 'matching-cut-cone-automorphisms.json').write_text(
        json.dumps(dict(permutations=autos, distinct_first_pair_representatives=representatives,
                        all_first_pair_representatives=all_representatives,
                        checked_assignments_per_permutation=1024), indent=2) + '\n')
    for name, gates, output in (('baseline15', baseline, baseline_output),
                                ('seed14', seed, seed_output)):
        artifact = dict(cut_inputs=13, gates=gates, output=output,
                        missing_edge=None if name == 'baseline15' else list(missing))
        (output_dir / f'matching-cut-cone-{name}.json').write_text(json.dumps(artifact, indent=2) + '\n')
    (output_dir / 'matching-cut-cone-seed26-embedded.json').write_text(
        json.dumps(dict(inputs=14, gates=full, output=39, missing_edge=missing_original,
                        target_errors=full_errors, checked_assignments=16384), indent=2) + '\n')
    print(json.dumps(dict(positive_rows=len(positives), negative_rows=len(negatives),
                          cut_inputs=13, baseline_cone_gates=15, target_cone_gates=14,
                          seed_cone_errors=seed_errors, embedded_seed_errors=full_errors,
                          checked_full_assignments=16384, automorphisms=len(autos),
                          first_pair_orbits=len(representatives))))


if __name__ == '__main__':
    main()
