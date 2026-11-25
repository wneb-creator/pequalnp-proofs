import argparse
import itertools
import json
from pathlib import Path

HEAWOOD = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
           (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
           (6,8),(6,9),(6,11)]
VARIABLES = [0,1,7,8,9,10,13]
LOCAL = {v:i for i,v in enumerate(VARIABLES)}
EDGES = [(LOCAL[a],LOCAL[b]) for a,b in HEAWOOD if a in (0,1)]
CUTS = [(3,6),(5,6),(4,5),(3,4)]


def graph_value(values,edges):
    return any(values[a] and values[b] for a,b in edges)


def evaluate(initial,gates):
    values = list(initial)
    for op,a,b in gates:
        assert op in (0,1) and 0 <= a < len(values) and 0 <= b < len(values)
        values.append((values[a] or values[b]) if op else (values[a] and values[b]))
    return values


def cut_values(mask):
    values = [bool(mask & (1 << i)) for i in range(7)]
    values.extend(values[a] or values[b] for a,b in CUTS)
    return values


def fixed_prefix():
    blocks = [(2,8,13,12),(3,11,12,7),(4,10,13,11),(5,9,10,12),(6,8,9,11)]
    gates,terms = [],[]
    for center,a,b,other in blocks:
        gates.append([1,a,b])
        pair = 13+len(gates)
        gates.append([1,pair,other])
        gates.append([0,center,13+len(gates)])
        terms.append(13+len(gates))
    output = terms[0]
    for term in terms[1:]:
        gates.append([1,output,term])
        output = 13+len(gates)
    assert len(gates) == 19 and output == 32
    return gates


def star_cone(missing=None):
    gates,terms = [],[]
    for left in range(2):
        neighbors = [b for a,b in EDGES if a == left and (a,b) != missing]
        wire = neighbors[0]
        for right in neighbors[1:]:
            gates.append([1,wire,right])
            wire = 10+len(gates)
        gates.append([0,left,wire])
        terms.append(10+len(gates))
    gates.append([1,terms[0],terms[1]])
    return gates,10+len(gates)


def embed(cone,output):
    gates = fixed_prefix()
    mapping = VARIABLES+[14,20,23,26]
    for op,a,b in cone:
        gates.append([op,mapping[a],mapping[b]])
        mapping.append(13+len(gates))
    gates.append([1,32,mapping[output]])
    return gates


def automorphisms():
    result = []
    cut_of = {tuple(sorted(pair)):7+i for i,pair in enumerate(CUTS)}
    for swap,flip_a,flip_b in itertools.product(range(2),repeat=3):
        perm = list(range(7))
        a = [3,5][::(-1 if flip_a else 1)]
        b = [4,6][::(-1 if flip_b else 1)]
        if swap:
            perm[0],perm[1] = 1,0
            perm[3],perm[5] = b
            perm[4],perm[6] = a
        else:
            perm[3],perm[5] = a
            perm[4],perm[6] = b
        perm.extend(cut_of[tuple(sorted((perm[x],perm[y])))] for x,y in CUTS)
        assert sorted(perm) == list(range(11))
        for mask in range(1 << 7):
            image_mask = sum(1 << perm[v] for v in range(7) if mask & (1 << v))
            old,new = cut_values(mask),cut_values(image_mask)
            assert all(old[v] == new[perm[v]] for v in range(11))
            assert graph_value(old,EDGES) == graph_value(new,EDGES)
        result.append(perm)
    assert len({tuple(p) for p in result}) == 8
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir',required=True)
    args = parser.parse_args()
    output_dir = Path(args.output_dir)
    positives = sorted((1 << a)|(1 << b) for a,b in EDGES)
    negatives = []
    for mask in range(1 << 7):
        if graph_value(cut_values(mask),EDGES):
            continue
        if all(graph_value(cut_values(mask|(1 << j)),EDGES)
               for j in range(7) if not mask & (1 << j)):
            negatives.append(mask)
    assert len(positives) == 6 and len(negatives) == 4
    for mask in range(1 << 7):
        if graph_value(cut_values(mask),EDGES):
            assert any(p & mask == p for p in positives)
        else:
            assert any(mask & n == mask for n in negatives)
    baseline,baseline_output = star_cone()
    seeds = []
    for original in ((0,8),(0,7)):
        missing = tuple(LOCAL[v] for v in original)
        gates,output = star_cone(missing)
        assert len(gates) == 6
        seeds.append((original,missing,gates,output))
        (output_dir/f'five-star-cut-cone-seed6-missing-{original[0]}-{original[1]}.json').write_text(
            json.dumps(dict(cut_inputs=11,gates=gates,output=output,
                            missing_local_edge=missing,missing_original_edge=original),indent=2)+'\n')
    for mask in range(1 << 7):
        initial = cut_values(mask)
        assert evaluate(initial,baseline)[baseline_output] == graph_value(initial,EDGES)
        for _,missing,gates,output in seeds:
            assert evaluate(initial,gates)[output] == graph_value(initial,[e for e in EDGES if e != missing])
    full_baseline = embed(baseline,baseline_output)
    full_seeds = [embed(gates,output) for _,_,gates,output in seeds]
    assert len(full_baseline) == 27 and all(len(s) == 26 for s in full_seeds)
    errors = [0,0]
    for mask in range(1 << 14):
        initial = [bool(mask & (1 << i)) for i in range(14)]
        target = graph_value(initial,HEAWOOD)
        assert evaluate(initial,full_baseline)[-1] == target
        for index,((original,_,_,_),gates) in enumerate(zip(seeds,full_seeds)):
            value = evaluate(initial,gates)[-1]
            assert value == graph_value(initial,[e for e in HEAWOOD if e != original])
            errors[index] += value != target
    rows = [dict(mask=m,value=int(m in positives),cuts=list(map(int,cut_values(m))))
            for m in sorted(positives+negatives)]
    data = dict(real_inputs=7,cut_inputs=11,cone_gate_budget=6,original_variables=VARIABLES,
                edges=EDGES,free_or_sums=CUTS,positive_rows=positives,negative_rows=negatives,
                rows=rows,fixed_gates=fixed_prefix(),fixed_cut_wires=[14,20,23,26],fixed_output=32,
                checked_residual_assignments=128,checked_full_assignments=16384,
                embedded_seed_errors=errors)
    (output_dir/'five-star-cut-cone-rows.json').write_text(json.dumps(data,indent=2)+'\n')
    (output_dir/'five-star-cut-cone-baseline7.json').write_text(
        json.dumps(dict(cut_inputs=11,gates=baseline,output=baseline_output),indent=2)+'\n')
    autos = automorphisms()
    representatives = sorted({min(tuple(sorted((p[a],p[b]))) for p in autos)
                              for a in range(11) for b in range(a,11)})
    (output_dir/'five-star-cut-cone-symmetries.json').write_text(
        json.dumps(dict(permutations=autos,all_first_pair_representatives=representatives,
                        checked_assignments_per_permutation=128),indent=2)+'\n')
    print(json.dumps(dict(positive_rows=6,negative_rows=4,cut_inputs=11,baseline_cone_gates=7,
                          target_cone_gates=6,seed_classes=2,embedded_seed_errors=errors,
                          automorphisms=len(autos),first_pair_orbits=len(representatives),
                          checked_full_assignments=16384)))


if __name__ == '__main__':
    main()
