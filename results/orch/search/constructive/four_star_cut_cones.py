import argparse
import itertools
import json
from pathlib import Path

HEAWOOD = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
           (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
           (6,8),(6,9),(6,11)]
FIXED = [0,3,5,6]
VARIABLES = [1,2,4,7,8,9,10,11,12,13]
LOCAL = {v:i for i,v in enumerate(VARIABLES)}
EDGES = [(LOCAL[a],LOCAL[b]) for a,b in HEAWOOD if a in (1,2,4)]
PAIR_LINE = {(0,1):7,(0,3):8,(2,3):9,(0,2):10,(1,3):11,(1,2):12}
NEIGHBORS = {i:sorted(PAIR_LINE[tuple(sorted((i,j)))] for j in range(4) if j != i)
             for i in range(4)}
PERMS = list(itertools.permutations(range(4)))


def action(choice,perm):
    result = [None]*4
    for i,j in enumerate(choice):
        result[perm[i]] = perm[j]
    return tuple(result)


def representatives():
    groups = {}
    for choice in itertools.product(*[[j for j in range(4) if j != i] for i in range(4)]):
        groups.setdefault(min(action(choice,p) for p in PERMS),[]).append(choice)
    assert sum(map(len,groups.values())) == 81 and len(groups) == 6
    return sorted(groups.items())


def full_permutation(perm):
    result = list(range(14))
    for i,v in enumerate(FIXED):
        result[v] = FIXED[perm[i]]
    for pair,line in PAIR_LINE.items():
        result[line] = PAIR_LINE[tuple(sorted(perm[i] for i in pair))]
    # The three remaining left points are determined by their two non-13 lines.
    color_pairs = {v:frozenset(b for a,b in HEAWOOD if a == v and b != 13) for v in (1,2,4)}
    color_of = {pair:v for v,pair in color_pairs.items()}
    for v,pair in color_pairs.items():
        result[v] = color_of[frozenset(result[line] for line in pair)]
    assert sorted(result) == list(range(14))
    assert {(result[a],result[b]) for a,b in HEAWOOD} == set(HEAWOOD)
    return result


def graph_value(values,edges):
    return any(values[a] and values[b] for a,b in edges)


def evaluate(initial,gates):
    values = list(initial)
    for op,a,b in gates:
        assert op in (0,1) and 0 <= a < len(values) and 0 <= b < len(values)
        values.append((values[a] or values[b]) if op else (values[a] and values[b]))
    return values


def cut_definitions(choice):
    definitions = []
    for i,j in enumerate(choice):
        excluded = PAIR_LINE[tuple(sorted((i,j)))]
        pair = [v for v in NEIGHBORS[i] if v != excluded]
        definitions.extend([list(map(LOCAL.get,pair)),list(map(LOCAL.get,NEIGHBORS[i]))])
    return definitions


def cut_values(mask,definitions):
    values = [bool(mask & (1 << i)) for i in range(10)]
    values.extend(any(values[v] for v in support) for support in definitions)
    return values


def fixed_prefix(choice):
    gates,cuts,terms = [],[],[]
    for i,j in enumerate(choice):
        excluded = PAIR_LINE[tuple(sorted((i,j)))]
        pair = [v for v in NEIGHBORS[i] if v != excluded]
        gates.append([1,pair[0],pair[1]])
        cuts.append(13+len(gates))
        gates.append([1,cuts[-1],excluded])
        cuts.append(13+len(gates))
        gates.append([0,FIXED[i],cuts[-1]])
        terms.append(13+len(gates))
    output = terms[0]
    for term in terms[1:]:
        gates.append([1,output,term])
        output = 13+len(gates)
    assert len(gates) == 15 and output == 28
    return gates,cuts


def star_cone(missing=None):
    gates,terms = [],[]
    for left in range(3):
        neighbors = [b for a,b in EDGES if a == left and (a,b) != missing]
        wire = neighbors[0]
        for right in neighbors[1:]:
            gates.append([1,wire,right])
            wire = 17+len(gates)
        gates.append([0,left,wire])
        terms.append(17+len(gates))
    output = terms[0]
    for term in terms[1:]:
        gates.append([1,output,term])
        output = 17+len(gates)
    return gates,output


def embed(choice,cone,output):
    gates,cuts = fixed_prefix(choice)
    mapping = VARIABLES+cuts
    for op,a,b in cone:
        gates.append([op,mapping[a],mapping[b]])
        mapping.append(13+len(gates))
    gates.append([1,28,mapping[output]])
    return gates


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir',required=True)
    args = parser.parse_args()
    output_dir = Path(args.output_dir)
    positives = sorted((1 << a)|(1 << b) for a,b in EDGES)
    negatives = []
    for mask in range(1 << 10):
        values = [bool(mask & (1 << i)) for i in range(10)]
        if graph_value(values,EDGES):
            continue
        if all(graph_value([bool((mask|(1 << j)) & (1 << i)) for i in range(10)],EDGES)
               for j in range(10) if not mask & (1 << j)):
            negatives.append(mask)
    assert len(positives) == 9 and len(negatives) == 8
    for mask in range(1 << 10):
        if graph_value([bool(mask & (1 << i)) for i in range(10)],EDGES):
            assert any(p & mask == p for p in positives)
        else:
            assert any(mask & n == mask for n in negatives)
    baseline,baseline_output = star_cone()
    seeds = []
    for original in ((1,7),(1,13)):
        missing = tuple(LOCAL[v] for v in original)
        gates,output = star_cone(missing)
        assert len(gates) == 10
        seeds.append((original,missing,gates,output))
        (output_dir/f'four-star-cut-cone-seed10-missing-{original[0]}-{original[1]}.json').write_text(
            json.dumps(dict(cut_inputs=18,gates=gates,output=output,
                            missing_local_edge=missing,missing_original_edge=original),indent=2)+'\n')
    (output_dir/'four-star-cut-cone-baseline11.json').write_text(
        json.dumps(dict(cut_inputs=18,gates=baseline,output=baseline_output),indent=2)+'\n')
    reports,symmetry_reports = [],[]
    for index,(choice,members) in enumerate(representatives()):
        definitions = cut_definitions(choice)
        rows = [dict(mask=m,value=int(m in positives),cuts=list(map(int,cut_values(m,definitions))))
                for m in sorted(positives+negatives)]
        for mask in range(1 << 10):
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
            assert evaluate(initial,full_baseline)[-1] == graph_value(initial,HEAWOOD)
            value = evaluate(initial,full_seed)[-1]
            assert value == graph_value(initial,[e for e in HEAWOOD if e != (1,7)])
            errors += value != graph_value(initial,HEAWOOD)
        fixed,cuts = fixed_prefix(choice)
        artifact = dict(variant=index,choice_excluded_neighbor=choice,choice_orbit_size=len(members),
                        choice_orbit_members=members,real_inputs=10,cut_inputs=18,cone_gate_budget=10,
                        original_variables=VARIABLES,edges=EDGES,free_or_supports=definitions,
                        positive_rows=positives,negative_rows=negatives,rows=rows,
                        fixed_gates=fixed,fixed_cut_wires=cuts,fixed_output=28,
                        checked_residual_assignments=1024,checked_full_assignments=16384,
                        embedded_seed_missing_edge=[1,7],embedded_seed_errors=errors)
        (output_dir/f'four-star-cut-cone-variant-{index}.json').write_text(json.dumps(artifact,indent=2)+'\n')
        stabilizer = []
        for perm in PERMS:
            full_perm = full_permutation(perm)
            target_choice = action(choice,perm)
            target_definitions = cut_definitions(target_choice)
            signal_perm = [LOCAL[full_perm[v]] for v in VARIABLES]
            signal_perm.extend(10+2*perm[i]+j for i in range(4) for j in range(2))
            for i,support in enumerate(definitions):
                mapped = {LOCAL[full_perm[VARIABLES[v]]] for v in support}
                assert mapped == set(target_definitions[signal_perm[10+i]-10])
            if target_choice == choice:
                for mask in range(1 << 10):
                    image_mask = sum(1 << signal_perm[v] for v in range(10) if mask & (1 << v))
                    old,new = cut_values(mask,definitions),cut_values(image_mask,definitions)
                    assert all(old[v] == new[signal_perm[v]] for v in range(18))
                stabilizer.append(signal_perm)
        assert len(stabilizer)*len(members) == 24
        symmetry_reports.append(dict(variant=index,choice=choice,cut_signal_stabilizer=stabilizer))
        reports.append(dict(variant=index,choice=choice,orbit_size=len(members),stabilizer=len(stabilizer),
                            positive_rows=9,negative_rows=8,embedded_seed_errors=errors))
    (output_dir/'four-star-cut-cone-symmetries.json').write_text(
        json.dumps(dict(variants=symmetry_reports,checked_assignments_per_stabilizer=1024),indent=2)+'\n')
    print(json.dumps(dict(variants=reports,baseline_cone_gates=11,target_cone_gates=10,
                          seed_classes=2,checked_full_assignments_per_variant=16384)))


if __name__ == '__main__':
    main()
