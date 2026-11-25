import argparse
import json
import sys
from pathlib import Path

from feature_gadget_sat import (run, extend, verify_problem, packed_verification,
                                evaluate)
from global_synthesis import canonicalize
from joint_feature_compatibility import (optional_prefix_constraints,
                                         used_feature_cardinality)
from symbolic_dirty_pair import require_symbolic_dirty_pair, dirty_pair_witness
from subset_cegis import stamp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'reduction_analysis'))
from punctured_mixed_assembler import assemble, raw_star_seed


def normalize_case(source):
    case = dict(source)
    case.update(name='punctured_four_arc', inputs=source['available_inputs'],
                input_original=source['raw_map'], max_gates=source['target_gates'],
                features=[dict(raw_indices=support) for support in source['features']])
    case['tests'] = [[extend(case, mask), label] for mask, label in case['raw_tests']]
    return case


def merged_phase(source):
    n = source['available_inputs']
    point_pair = source['raw_inputs'] + source['features'].index([0, 1])
    neighborhood = sorted({v for u, v in source['edges'] if u in (0, 1)})
    pair_index, pair = next((i, support) for i, support in enumerate(source['features'])
                           if len(support) == 2 and set(support) <= set(neighborhood))
    gates = []

    def gate(op, left, right):
        gates.append([op, *sorted((left, right))])
        return n + len(gates) - 1

    def disjoin(wires):
        value, *rest = wires
        for wire in rest:
            value = gate(1, value, wire)
        return value

    lines = disjoin([source['raw_inputs'] + pair_index] +
                    [line for line in neighborhood if line not in pair])
    terms = [gate(0, point_pair, lines)]
    for owner in (2, 3):
        lines = disjoin([v for u, v in source['edges'] if u == owner])
        terms.append(gate(0, owner, lines))
    disjoin(terms)
    assert len(gates) == source['target_gates'] == 15
    return canonicalize(gates, n)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('packet', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--phase-file', type=Path)
    parser.add_argument('--seconds', type=int, default=300)
    parser.add_argument('--rounds', type=int, default=4)
    parser.add_argument('--seed', type=int, default=57915)
    parser.add_argument('--and-count', type=int, default=5)
    parser.add_argument('--symbolic-dirty', action='store_true')
    args = parser.parse_args()
    assert args.and_count >= 5
    source = json.loads(args.packet.read_text())
    case = normalize_case(source)
    assert (case['raw_inputs'], case['inputs'], case['max_gates']) == (13, 37, 15)
    assert len(case['edges']) == 14 and len(case['raw_tests']) == 30
    witnesses = verify_problem(case)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'problem.json').write_text(json.dumps(case))
    (args.output / 'direct-essential-witnesses.json').write_text(json.dumps(witnesses))
    baseline, baseline_output = raw_star_seed(source)
    assert packed_verification(case, baseline)['false_positives'] == 0
    assert packed_verification(case, baseline)['false_negatives'] == 0
    calibration = assemble(source, baseline, baseline_output)
    assert len(baseline) == 17 and calibration['full_size'] == 65
    geometry = json.loads((Path(__file__).resolve().parents[2] /
                           'circuit_search' / 'geometry.json').read_text())
    full_tests = [((1 << a) | (1 << b), True) for a, b in geometry['edges']]
    full_tests += [(p | (l << 13), False) for p, l in geometry['maximal_independent_sets']]
    assert all(evaluate(calibration['gates'], mask, 26) == label for mask, label in full_tests)
    (args.output / 'baseline-full65.json').write_text(json.dumps(calibration))
    if args.phase_file:
        phase = json.loads(args.phase_file.read_text())
        if isinstance(phase, dict):
            phase = phase['gates']
    else:
        phase = merged_phase(source)
    assert len(phase) == 15
    phase = canonicalize(phase, case['inputs'])
    phase_assembly = assemble(source, phase)
    assert phase_assembly['full_size'] <= 63
    phase_truth = packed_verification(case, phase)
    (args.output / 'phase.json').write_text(json.dumps(dict(gates=phase, truth=phase_truth,
        and_count=sum(op == 0 for op, _, _ in phase), scope='Hints only; target AND count may differ.')))
    stamp('PUNCTURED FOUR VERIFIED', 'raw13 available37 positives14 negatives16',
          'outside47 target15; baseline17/full65', 'phase', phase_truth)

    def compatibility(cnf, selected, problem):
        used = optional_prefix_constraints(cnf, selected, source['optional_groups'],
                                           problem['inputs'])
        used_feature_cardinality(cnf, selected, problem['raw_inputs'], problem['inputs'],
                                 len(selected) - problem['raw_inputs'] + 1, used)

    def target_constraints(cnf, selected, problem):
        compatibility(cnf, selected, problem)
        if args.symbolic_dirty:
            require_symbolic_dirty_pair(cnf, selected, problem)

    def actual_assembly(problem, gates):
        if args.symbolic_dirty:
            witness = dirty_pair_witness(problem, gates)
            assert witness is not None
            (args.output / 'symbolic-dirty-witness.json').write_text(json.dumps(witness))
        result = assemble(source, gates)
        assert result['core_size'] <= 15 and result['full_size'] <= 63
        (args.output / 'exact-assembly.json').write_text(json.dumps(result))
        return result['gates']

    options = dict(crossings=True, kraft=True, kraft_exponential=True,
                   min_and_count=args.and_count, and_count=args.and_count,
                   assembler=actual_assembly, sufficient_for_full63=True)
    run(case, args.output / 'baseline', 20, args.seed, fixed=True,
        extra_constraints=compatibility, **options)
    run(case, args.output / 'search', args.seconds, args.seed + 1,
        phase_seed=phase, extra_constraints=target_constraints,
        solve_rounds=args.rounds, **options)


if __name__ == '__main__':
    main()
