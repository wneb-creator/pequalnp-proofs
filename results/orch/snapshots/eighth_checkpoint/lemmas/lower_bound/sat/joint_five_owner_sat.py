import argparse
import json
import sys
from pathlib import Path

from feature_gadget_sat import (run, star_seed, verify_problem, packed_verification,
                                evaluate, symmetry_phase)
from global_synthesis import canonicalize
import five_owner_and_samples
from template_feature_compatibility import (template_feature_constraints,
                                            choose_compatible_templates)
from subset_cegis import stamp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'algebra_strategy'))
from assemble_five_owner import assemble_five


def groups(case):
    return [dict(inputs=owner['feature_inputs'], templates=owner['zero_extra_templates'])
            for owner in case['outside_owners']]


def compatibility(cnf, selected, case):
    return template_feature_constraints(cnf, selected, case['raw_inputs'], case['inputs'],
                                        groups(case))


def assemble(case, gates):
    choose_compatible_templates(gates, groups(case))
    full, metadata = assemble_five(case, gates)
    assert metadata['prefix_extra_cost'] == 0 and metadata['outside_gates'] == 39
    assert metadata['within_budget']
    return full


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('pack', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--phase-file', type=Path, required=True)
    parser.add_argument('--phase-index', type=int, default=0)
    parser.add_argument('--symmetry-data', type=Path)
    parser.add_argument('--seconds', type=int, default=300)
    parser.add_argument('--rounds', type=int, default=1)
    parser.add_argument('--seed', type=int, default=57741)
    parser.add_argument('--and-count', type=int, default=5)
    parser.add_argument('--min-and-count', type=int, default=5)
    parser.add_argument('--crossings', action='store_true')
    parser.add_argument('--kraft', action='store_true')
    parser.add_argument('--kraft-exponential', action='store_true')
    parser.add_argument('--and-false-samples', type=int, default=0)
    parser.add_argument('--and-true-samples', type=int, default=0)
    parser.add_argument('--require-dirty-pair', action='store_true')
    parser.add_argument('--and-true-census', type=Path,
                        default=Path(__file__).resolve().parents[2] /
                        'reduction_analysis' / 'five_owner_forced_active_census.json')
    args = parser.parse_args()
    case = json.loads(args.pack.read_text())[0]
    witnesses = verify_problem(case)
    assert (case['raw_inputs'], case['inputs'], case['max_gates']) == (16, 52, 23)
    assert len([mask for mask, label in case['raw_tests'] if not label]) == 30
    symmetry = json.loads(args.symmetry_data.read_text()) if args.symmetry_data else None
    if symmetry is not None:
        assert (symmetry['inputs'], symmetry['raw_inputs'], symmetry['edges']) == (
            case['inputs'], case['raw_inputs'], case['edges'])
    phase = json.loads(args.phase_file.read_text())
    if isinstance(phase, dict):
        phase = phase['gates']
    elif isinstance(phase[0], dict):
        phase = phase[args.phase_index]['gates']
    phase = canonicalize(phase, case['inputs'])
    if symmetry is not None:
        phase = symmetry_phase(phase, case['inputs'], symmetry)
    choose_compatible_templates(phase, groups(case))
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'problem.json').write_text(json.dumps(case))
    (args.output / 'direct-essential-witnesses.json').write_text(json.dumps(witnesses))
    samples = five_owner_and_samples.prepare(case, phase, args.and_false_samples,
                                             args.and_true_samples, args.and_true_census)
    (args.output / 'internal-and-samples.json').write_text(json.dumps(samples))
    dirty = five_owner_and_samples.dirty_pairs(case) if args.require_dirty_pair else []
    (args.output / 'required-dirty-pairs.json').write_text(json.dumps(dirty))
    baseline = star_seed(case)
    baseline_truth = packed_verification(case, baseline)
    assert baseline_truth['false_positives'] == baseline_truth['false_negatives'] == 0
    baseline_full, report = assemble_five(case, baseline)
    assert report['gates'] == 64 and report['prefix_extra_cost'] == 0
    geometry = json.loads((Path(__file__).resolve().parents[2] /
                           'circuit_search' / 'geometry.json').read_text())
    full_tests = [((1 << a) | (1 << b), True) for a, b in geometry['edges']]
    full_tests += [(p | (l << 13), False) for p, l in geometry['maximal_independent_sets']]
    assert all(evaluate(baseline_full, mask, 26) == label for mask, label in full_tests)
    (args.output / 'baseline-assembly.json').write_text(json.dumps(report))
    stamp('JOINT FIVE-OWNER BASIS VERIFIED', len(witnesses), 'raw inputs',
          len(case['features']), 'features', [len(g['templates']) for g in groups(case)])
    stamp('INTERNAL AND SAMPLES', len(samples), 'false', sum(not s['value'] for s in samples),
          'true', sum(s['value'] for s in samples), 'guarded_by_AND_count_at_most_5')
    stamp('REQUIRED DIRTY PAIR FAMILY', len(dirty), 'target_only')

    def constraints(cnf, selected, problem):
        compatibility(cnf, selected, problem)
        five_owner_and_samples.add(cnf, selected, problem, samples, phase)

    def target_constraints(cnf, selected, problem):
        compatibility(cnf, selected, problem)
        five_owner_and_samples.add(cnf, selected, problem, samples, phase, dirty)

    options = dict(crossings=args.crossings, kraft=args.kraft,
                   kraft_exponential=args.kraft_exponential, symmetry=symmetry,
                   assembler=assemble,
                   sufficient_for_full63=True, min_and_count=args.min_and_count)
    run(case, args.output / 'baseline', 20, args.seed, fixed=True,
        and_count=max(args.and_count, args.min_and_count), extra_constraints=constraints, **options)
    run(case, args.output / 'search', args.seconds, args.seed + 1,
        phase_seed=phase, and_count=args.and_count, extra_constraints=target_constraints,
        solve_rounds=args.rounds, **options)


if __name__ == '__main__':
    main()
