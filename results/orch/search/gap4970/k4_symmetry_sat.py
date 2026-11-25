"""Optional K4-incidence first-gate symmetry and minimum-AND search cuts."""
import argparse
import hashlib
import itertools
import json
import resource
from pathlib import Path

import serve_sat
from operator_count_sat import add_at_most


def automorphisms():
    pairs = list(itertools.combinations(range(4), 2))
    index = {pair: i for i, pair in enumerate(pairs)}
    maps = []
    for perm in itertools.permutations(range(4)):
        maps.append(list(perm) + [4 + index[tuple(sorted((perm[a], perm[b])))] for a, b in pairs])
    return maps


def pair_orbits():
    maps = automorphisms()
    pairs = list(itertools.combinations_with_replacement(range(10), 2))
    representative = {
        pair: min(tuple(sorted((perm[pair[0]], perm[pair[1]]))) for perm in maps)
        for pair in pairs}
    p, l, edges = serve_sat.graph_data('k4inc')
    original = {(a, p + b) for a, b in edges}
    for perm in maps:
        assert {(perm[a], perm[b]) for a, b in original} == original
        assert all((i < p) == (perm[i] < p) for i in range(p + l))
    representatives = sorted(set(representative.values()))
    assert len(maps) == 24 and len(representatives) == 7
    return representative, representatives


def star_control():
    p, l, edges = serve_sat.graph_data('k4inc')
    n = p + l
    gates = []
    products = []
    for a in range(p):
        leaves = [p + b for aa, b in edges if aa == a]
        assert len(leaves) == 3
        gates.append([1, leaves[0], leaves[1]])
        first = n + len(gates) - 1
        gates.append([1, leaves[2], first])
        root = n + len(gates) - 1
        gates.append([0, a, root])
        products.append(n + len(gates) - 1)
    output = products[0]
    for other in products[1:]:
        gates.append([1, *sorted((output, other))])
        output = n + len(gates) - 1
    assert len(gates) == 15
    return gates, output


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--gates', type=int, default=14)
    parser.add_argument('--minimum-and', type=int, default=4)
    parser.add_argument('--seconds', type=int, default=30)
    parser.add_argument('--memory-mib', type=int, default=512)
    parser.add_argument('--output', required=True)
    parser.add_argument('--pin-star-control', action='store_true')
    args = parser.parse_args()
    args.graph = 'k4inc'
    args.output_before_last = False
    args.generate_only = False
    assert 0 <= args.minimum_and <= args.gates
    resource.setrlimit(resource.RLIMIT_AS, (args.memory_mib * 1024 * 1024,) * 2)
    representative, representatives = pair_orbits()
    frozen = serve_sat.make_problem

    def with_cuts(*positional, **keywords):
        encoded = frozen(*positional, **keywords)
        cnf, ops, selectors, outputs = encoded[:4]
        for (a, b), rep in representative.items():
            if (a, b) != rep:
                cnf.clause(-selectors[0][0][a], -selectors[0][1][b])
        add_at_most(cnf, ops, args.gates - args.minimum_and)
        if args.pin_star_control:
            gates, output = star_control()
            assert args.gates == len(gates)
            for g, (op, a, b) in enumerate(gates):
                cnf.clause(ops[g] if op else -ops[g])
                cnf.clause(selectors[g][0][a])
                cnf.clause(selectors[g][1][b])
            cnf.clause(outputs[output - 10])
        return encoded

    serve_sat.make_problem = with_cuts
    result = serve_sat.main(args)
    result['additional_constraints'] = {
        'first_gate_pair_orbit_representatives': representatives,
        'automorphism_count': 24, 'minimum_and': args.minimum_and,
        'memory_limit_mib': args.memory_mib, 'pinned_star_control': args.pin_star_control,
        'base_encoder_sha256': hashlib.sha256(Path(serve_sat.__file__).read_bytes()).hexdigest(),
        'interpretation': 'SAT witnesses are fully verified; UNSAT remains uncertified and subject to stated cuts.'}
    if result['status'] == 'SAT':
        and_count = sum(not op for op, _, _ in result['circuit'])
        assert and_count >= args.minimum_and
        assert tuple(result['circuit'][0][1:]) in representatives
        result['operation_counts'] = {'AND': and_count, 'OR': args.gates - and_count}
    Path(args.output).with_suffix('.result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
