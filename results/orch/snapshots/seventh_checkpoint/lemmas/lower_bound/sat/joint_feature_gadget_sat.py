import argparse
import json
import sys
from pathlib import Path

from feature_gadget_sat import run, star_seed, verify_problem, packed_verification, evaluate
from joint_feature_compatibility import (optional_prefix_constraints, used_optional_prefixes,
                                         used_feature_cardinality)
from joint_feature_cost import copy_credited_prefix_constraints, syntactic_budget
from subset_cegis import stamp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'circuit_search'))
from assemble_joint_four import assemble_joint


def compatibility(cnf, selected, case):
    used = optional_prefix_constraints(cnf, selected, case['optional_prefix_groups'],
                                       case['inputs'])
    return used_feature_cardinality(cnf, selected, case['raw_inputs'], case['inputs'],
                                    len(selected) - case['raw_inputs'] + 1, used)


def assemble(case, gates):
    used_optional_prefixes(gates, case['optional_prefix_groups'])
    full, metadata = assemble_joint(case, gates)
    assert metadata['prefix_extra_cost'] == 0
    assert metadata['outside_gates'] == 44
    assert metadata['within_budget']
    return full


def compatibility_with_copy_credit(cnf, selected, case):
    return copy_credited_prefix_constraints(cnf, selected, case['optional_prefix_groups'],
                                           case['raw_inputs'], case['inputs'])


def assemble_with_copy_credit(case, gates):
    credit = syntactic_budget(gates, case['optional_prefix_groups'])
    assert credit['within_budget']
    full, metadata = assemble_joint(case, gates)
    assert metadata['prefix_extra_cost'] <= credit['extra']
    assert metadata['core_gates'] <= len(gates) - credit['copies']
    assert metadata['outside_gates'] == 44 + metadata['prefix_extra_cost']
    assert metadata['within_budget']
    return full


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('pack', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--phase-file', type=Path, required=True)
    parser.add_argument('--symmetry-data', type=Path)
    parser.add_argument('--seconds', type=int, default=300)
    parser.add_argument('--seed', type=int, default=57581)
    parser.add_argument('--and-count', type=int)
    parser.add_argument('--min-and-count', type=int, default=5)
    parser.add_argument('--copy-credit', action='store_true')
    parser.add_argument('--crossings', action='store_true')
    parser.add_argument('--kraft', action='store_true')
    parser.add_argument('--kraft-exponential', action='store_true')
    parser.add_argument('--zero-wildcards', action='store_true')
    args = parser.parse_args()
    case = json.loads(args.pack.read_text())[0]
    witnesses = verify_problem(case)
    groups = case['optional_prefix_groups']
    assert len(groups) == 6 and all(len(group) == 3 for group in groups)
    assert len({wire for group in groups for wire in group}) == 18
    symmetry = json.loads(args.symmetry_data.read_text()) if args.symmetry_data else None
    if symmetry is not None:
        assert (symmetry['inputs'], symmetry['raw_inputs'], symmetry['edges']) == (
            case['inputs'], case['raw_inputs'], case['edges'])
    phase = json.loads(args.phase_file.read_text())
    if isinstance(phase, dict):
        phase = phase['gates']
    elif isinstance(phase[0], dict):
        phase = phase[0]['gates']
    if args.copy_credit:
        assert syntactic_budget(phase, groups)['within_budget']
    else:
        used_optional_prefixes(phase, groups)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'problem.json').write_text(json.dumps(case))
    (args.output / 'direct-essential-witnesses.json').write_text(json.dumps(witnesses))
    baseline = star_seed(case)
    baseline_truth = packed_verification(case, baseline)
    assert baseline_truth['false_positives'] == baseline_truth['false_negatives'] == 0
    baseline_full, baseline_report = assemble_joint(case, baseline)
    assert baseline_report['gates'] == 64 and baseline_report['prefix_extra_cost'] == 0
    geometry = json.loads((Path(__file__).resolve().parents[2] /
                           'circuit_search' / 'geometry.json').read_text())
    full_tests = [((1 << a) | (1 << b), True) for a, b in geometry['edges']]
    full_tests += [(p | (l << 13), False) for p, l in geometry['maximal_independent_sets']]
    assert all(evaluate(baseline_full, mask, 26) == label for mask, label in full_tests)
    (args.output / 'baseline-assembly.json').write_text(json.dumps(baseline_report))
    stamp('JOINT FEATURE BASIS VERIFIED', len(witnesses), 'raw inputs',
          len(case['features']), 'features', len(groups), 'optional groups')
    options = dict(crossings=args.crossings, kraft=args.kraft,
                   kraft_exponential=args.kraft_exponential,
                   zero_wildcards=args.zero_wildcards, symmetry=symmetry,
                   extra_constraints=(compatibility_with_copy_credit if args.copy_credit
                                      else compatibility),
                   assembler=(assemble_with_copy_credit if args.copy_credit else assemble),
                   sufficient_for_full63=True)
    calibration_ands = max(args.and_count or 4, args.min_and_count)
    run(case, args.output / 'baseline', 20, args.seed, fixed=True,
        and_count=calibration_ands, min_and_count=args.min_and_count, **options)
    run(case, args.output / 'search', args.seconds, args.seed + 1,
        phase_seed=phase, and_count=args.and_count,
        min_and_count=args.min_and_count, **options)


if __name__ == '__main__':
    main()
