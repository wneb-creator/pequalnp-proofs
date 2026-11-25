import argparse
import itertools
import json
from pathlib import Path


HEAWOOD = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
           (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
           (6,8),(6,9),(6,11)]
VARIABLES = [3,4,5,6,7,8,9,10,11,12,13]
LOCAL = {v:i for i,v in enumerate(VARIABLES)}
EDGES = [(LOCAL[a],LOCAL[b]) for a,b in HEAWOOD if a in (3,4,5,6)]
NEIGHBORS = {v:[b for a,b in HEAWOOD if a == v] for v in (0,1,2)}
EXTERNAL = {0:10,1:9,2:12}
SHARED = {(0,1):7,(0,2):8,(1,2):13}
PERMS = list(itertools.permutations(range(3)))


def action(choice, perm):
    result = [None] * 3
    for i, value in enumerate(choice):
        result[perm[i]] = -1 if value == -1 else perm[value]
    return tuple(result)


def representatives():
    groups = {}
    for choice in itertools.product(*[[-1] + [j for j in range(3) if j != i]
                                      for i in range(3)]):
        representative = min(action(choice, p) for p in PERMS)
        groups.setdefault(representative, []).append(choice)
    assert sum(map(len, groups.values())) == 27 and len(groups) == 7
    return sorted(groups.items())


def full_permutation(perm):
    result = list(range(14))
    result[:3] = perm
    third = {(0,1):3,(0,2):6,(1,2):4}
    for pair, vertex in third.items():
        result[vertex] = third[tuple(sorted(perm[i] for i in pair))]
    for pair, line in SHARED.items():
        result[line] = SHARED[tuple(sorted(perm[i] for i in pair))]
    for vertex,line in EXTERNAL.items():
        result[line] = EXTERNAL[perm[vertex]]
    assert sorted(result) == list(range(14))
    assert {(result[a],result[b]) for a,b in HEAWOOD} == set(HEAWOOD)
    return result


def evaluate(initial, gates):
    values = list(initial)
    for op,a,b in gates:
        assert op in (0,1) and 0 <= a < len(values) and 0 <= b < len(values)
        values.append((values[a] or values[b]) if op else (values[a] and values[b]))
    return values


def graph_value(values, edges):
    return any(values[a] and values[b] for a,b in edges)


def cut_definitions(choice):
    result = []
    for i, value in enumerate(choice):
        excluded = EXTERNAL[i] if value == -1 else SHARED[tuple(sorted((i,value)))]
        pair = [v for v in NEIGHBORS[i] if v != excluded]
        result.extend([list(map(LOCAL.get, pair)), list(map(LOCAL.get, NEIGHBORS[i]))])
    return result


def cut_values(mask, definitions):
    values = [bool(mask & (1 << i)) for i in range(11)]
    values.extend(any(values[v] for v in support) for support in definitions)
    return values


def fixed_prefix(choice):
    gates, cuts, terms = [], [], []
    for i, value in enumerate(choice):
        excluded = EXTERNAL[i] if value == -1 else SHARED[tuple(sorted((i,value)))]
        pair = [v for v in NEIGHBORS[i] if v != excluded]
        gates.append([1, pair[0], pair[1]])
        cuts.append(13 + len(gates))
        gates.append([1, cuts[-1], excluded])
        cuts.append(13 + len(gates))
        gates.append([0, i, cuts[-1]])
        terms.append(13 + len(gates))
    gates.append([1, terms[0], terms[1]])
    gates.append([1, 13 + len(gates), terms[2]])
    assert len(gates) == 11
    return gates, cuts


def star_cone(missing=None):
    gates, terms = [], []
    for left in range(4):
        neighbors = [b for a,b in EDGES if a == left and (a,b) != missing]
        wire = neighbors[0]
        for right in neighbors[1:]:
            gates.append([1, wire, right])
            wire = 16 + len(gates)
        gates.append([0, left, wire])
        terms.append(16 + len(gates))
    output = terms[0]
    for term in terms[1:]:
        gates.append([1, output, term])
        output = 16 + len(gates)
    return gates, output


def embed(choice, cone, output):
    gates, cuts = fixed_prefix(choice)
    mapping = VARIABLES + cuts
    for op,a,b in cone:
        gates.append([op, mapping[a], mapping[b]])
        mapping.append(13 + len(gates))
    gates.append([1, 24, mapping[output]])
    return gates


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', required=True)
    args = parser.parse_args()
    output_dir = Path(args.output_dir)
    positives = sorted((1 << a) | (1 << b) for a,b in EDGES)
    negatives = []
    for mask in range(1 << 11):
        values = [bool(mask & (1 << i)) for i in range(11)]
        if graph_value(values, EDGES):
            continue
        if all(graph_value([bool((mask | (1 << j)) & (1 << i)) for i in range(11)], EDGES)
               for j in range(11) if not mask & (1 << j)):
            negatives.append(mask)
    for mask in range(1 << 11):
        if graph_value([bool(mask & (1 << i)) for i in range(11)], EDGES):
            assert any(p & mask == p for p in positives)
        else:
            assert any(mask & n == mask for n in negatives)
    baseline, baseline_output = star_cone()
    missing_originals = [(3,7),(3,11),(3,12),(5,9)]
    seeds = []
    for original in missing_originals:
        missing = tuple(LOCAL[v] for v in original)
        gates, output = star_cone(missing)
        assert len(gates) == 14
        seeds.append((original, missing, gates, output))
        artifact = dict(cut_inputs=17, gates=gates, output=output,
                        missing_local_edge=missing, missing_original_edge=original)
        name = f'noncollinear-cut-cone-seed14-missing-{original[0]}-{original[1]}.json'
        (output_dir / name).write_text(json.dumps(artifact, indent=2) + '\n')
    (output_dir / 'noncollinear-cut-cone-baseline15.json').write_text(
        json.dumps(dict(cut_inputs=17,gates=baseline,output=baseline_output),indent=2)+'\n')
    reports = []
    symmetry_reports = []
    for index,(choice,members) in enumerate(representatives()):
        definitions = cut_definitions(choice)
        rows = [dict(mask=m, value=int(m in positives),
                     cuts=list(map(int,cut_values(m,definitions))))
                for m in sorted(positives + negatives)]
        for mask in range(1 << 11):
            initial = cut_values(mask,definitions)
            assert evaluate(initial,baseline)[baseline_output] == graph_value(initial,EDGES)
            for _,missing,gates,output in seeds:
                assert evaluate(initial,gates)[output] == graph_value(initial,[e for e in EDGES if e != missing])
        full_baseline = embed(choice,baseline,baseline_output)
        full_seed = embed(choice,seeds[0][2],seeds[0][3])
        assert len(full_baseline) == 27 and len(full_seed) == 26
        errors = 0
        for mask in range(1 << 14):
            initial = [bool(mask & (1 << i)) for i in range(14)]
            target = graph_value(initial,HEAWOOD)
            assert evaluate(initial,full_baseline)[-1] == target
            value = evaluate(initial,full_seed)[-1]
            assert value == graph_value(initial,[e for e in HEAWOOD if e != (3,7)])
            errors += value != target
        fixed,cuts = fixed_prefix(choice)
        artifact = dict(variant=index,choice_excluded=choice,choice_orbit_size=len(members),
                        choice_orbit_members=members,real_inputs=11,cut_inputs=17,
                        cone_gate_budget=14,original_variables=VARIABLES,edges=EDGES,
                        free_or_supports=definitions,positive_rows=positives,
                        negative_rows=negatives,rows=rows,fixed_gates=fixed,
                        fixed_cut_wires=cuts,fixed_output=24,
                        checked_residual_assignments=2048,checked_full_assignments=16384,
                        embedded_seed_missing_edge=[3,7],embedded_seed_errors=errors)
        (output_dir/f'noncollinear-cut-cone-variant-{index}.json').write_text(json.dumps(artifact,indent=2)+'\n')
        reports.append(dict(variant=index,choice=choice,orbit_size=len(members),
                            positive_rows=len(positives),negative_rows=len(negatives),
                            embedded_seed_errors=errors))
        stabilizer = []
        for perm in PERMS:
            full_perm = full_permutation(perm)
            target_choice = action(choice,perm)
            target_definitions = cut_definitions(target_choice)
            signal_perm = [LOCAL[full_perm[v]] for v in VARIABLES]
            signal_perm.extend(11 + 2*perm[i] + j for i in range(3) for j in range(2))
            for i,support in enumerate(definitions):
                mapped = {LOCAL[full_perm[VARIABLES[v]]] for v in support}
                assert mapped == set(target_definitions[signal_perm[11+i]-11])
            if target_choice == choice:
                for mask in range(1 << 11):
                    image_mask = sum(1 << signal_perm[v] for v in range(11) if mask & (1 << v))
                    old,new = cut_values(mask,definitions),cut_values(image_mask,definitions)
                    assert all(old[v] == new[signal_perm[v]] for v in range(17))
                stabilizer.append(signal_perm)
        assert len(stabilizer)*len(members) == 6
        symmetry_reports.append(dict(variant=index,choice=choice,
                                     cut_signal_stabilizer=stabilizer))
    (output_dir/'noncollinear-cut-cone-symmetries.json').write_text(
        json.dumps(dict(variants=symmetry_reports,checked_assignments_per_stabilizer=2048),indent=2)+'\n')
    print(json.dumps(dict(variants=reports,baseline_cone_gates=len(baseline),
                          seed_classes=len(seeds),checked_full_assignments_per_variant=16384)))


if __name__ == '__main__':
    main()
