"""Analyze all-positive near-circuits and prepare exact-target repairs; no solver.

The source may have false positives, but all 16 target edges must be accepted.
Every generated formula retains all target boundary constraints. Output is free;
there is no first-junk, second-junk, clean-prefix, liveness or tail restriction.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path('/tmp/oec/pequalnp-pilot-18')
RESCHEDULED_SHA = '9276816606eb7ab1738b277bcf4c34f128b63e5158a23d54debbaadfaf88fd8c'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def dependencies():
    path = ROOT / 'orch/S02/generate_rescheduled_repairs.py'
    if sha(path.read_bytes()) != RESCHEDULED_SHA:
        raise ValueError('Reviewed free-output helper SHA256 mismatch')
    spec = importlib.util.spec_from_file_location('positive_free_output_helper', path)
    free = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(free)
    distance, helper, base = free.dependencies()
    return free, distance, helper, base


def suppressed_output(data, mask, suppressed):
    values = [bool(mask & (1 << v)) for v in range(11)] + [False, True]
    for g, (op, a, b) in enumerate(data['gates']):
        value = values[a] and values[b] if op == 'and' else values[a] or values[b]
        values.append(False if g == suppressed else value)
    return values[data['output']]


def analyze(data, helper):
    summary = helper.source_summary(data)
    edges = [(1 << a) | (1 << b) for a, b in helper.EDGES]
    accepted_edges = [m for m in edges if helper.scalar_values(data['gates'], m)[data['output']]]
    negatives = summary['boundary_false_positive_masks']
    impact = []
    for g in range(len(data['gates'])):
        fixed = [m for m in negatives if not suppressed_output(data, m, g)]
        lost = [m for m in accepted_edges if not suppressed_output(data, m, g)]
        impact.append({'gate': g, 'fixed_false_positive_masks': fixed,
                       'lost_positive_edge_masks': lost,
                       'negative_gain': len(fixed), 'positive_loss': len(lost)})
    order = sorted(range(len(impact)), key=lambda g: (
        -(impact[g]['negative_gain'] / (1 + impact[g]['positive_loss'])),
        -impact[g]['negative_gain'], impact[g]['positive_loss'], g))
    return {**summary, 'all_positive_edges': not summary['boundary_false_negative_masks'],
            'suppression_impact': impact, 'negative_repair_gate_order': order,
            'ranking_is_heuristic_not_a_soundness_constraint': True}


def local_free_output(helper, base, data, holes):
    cnf, meta = helper.repair(base, data, holes)
    marker = [meta['output_selectors'][data['output']]]
    helper.require(cnf.clauses.count(marker) == 1 and meta['pin_clauses'][-1] == marker,
                   'Expected unique explicit output pin')
    meta['output_pinned_parent_sha256'] = sha(helper.dimacs(cnf))
    meta['removed_output_pin_index'] = cnf.clauses.index(marker)
    cnf.clauses.remove(marker)
    meta['pin_clauses'].pop()
    meta.pop('fixed_output_wire')
    meta.update(output_selection_free=True, seed_output_wire=data['output'],
                removed_output_pin=marker, clauses=len(cnf.clauses))
    return cnf, meta


def build_cases(free, distance, helper, base, data, summary, budgets, local_counts):
    for budget in budgets:
        cnf, meta = free.unrestricted_distance(distance, helper, base, data, budget)
        yield f'distance-k{budget:02d}', cnf, meta, {'budget': budget}
    for count in local_counts:
        holes = sorted(summary['negative_repair_gate_order'][:count])
        cnf, meta = local_free_output(helper, base, data, holes)
        yield f'negative-free{count:02d}', cnf, meta, {'free_gates': holes}


def prepare(source, output, budgets, local_counts, max_false_positive_rows, analysis_only):
    if output.exists():
        raise ValueError('Output directory must be fresh')
    if (not 1 <= max_false_positive_rows <= 24 or
        budgets != sorted(set(budgets)) or not all(0 <= k <= 7 for k in budgets) or
        local_counts != sorted(set(local_counts)) or not all(1 <= k <= 7 for k in local_counts) or
        (not analysis_only and not budgets and not local_counts)):
        raise ValueError('Invalid bounded family parameters')
    free, distance, helper, base = dependencies()
    raw = source.read_bytes()
    validator = helper.load(ROOT / 'validate_raw_candidate.py', 'positive_structure_validator', helper.RAW_SHA)
    offset, gates, outwire = validator.check_structure(json.loads(raw))
    helper.require(offset == 13 and len(gates) == 21, 'Expected 21 augmented gates')
    data = {'inputs': 11, 'gate_wire_offset': 13, 'size': 21, 'output': outwire,
            'gates': [[op, *sorted((a, b))] for op, a, b in gates]}
    summary = analyze(data, helper)
    if not analysis_only:
        helper.require(summary['all_positive_edges'] and summary['full_2048_false_negative_count'] == 0,
                       'Source misses target positive inputs')
        helper.require(0 < len(summary['boundary_false_positive_masks']) <= max_false_positive_rows,
                       'Source must be inexact with bounded positive false-positive count')
    output.mkdir(parents=True, exist_ok=False)
    (output / 'source.json').write_bytes(raw)
    (output / 'source-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    manifest = {'kind': 'candidate_only_all_positive_negative_error_repairs', 'complete': False,
                'analysis_only': analysis_only, 'source_sha256': sha(raw),
                'source_summary_sha256': sha((output / 'source-summary.json').read_bytes()),
                'program_sha256': sha(Path(__file__).read_bytes()), 'free_output_helper_sha256': RESCHEDULED_SHA,
                'distance_helper_sha256': free.DISTANCE_SHA, 'local_helper_sha256': distance.HELPER_SHA,
                'base_generator_sha256': helper.BASE_SHA, 'assigned_shard_exhaustion': False,
                'output_selection_free': True, 'budgets': budgets, 'local_counts': local_counts,
                'max_false_positive_rows': max_false_positive_rows, 'cases': []}
    if not analysis_only:
        for name, cnf, meta, extra in build_cases(free, distance, helper, base, data, summary, budgets, local_counts):
            meta.update(program=Path(__file__).name, program_sha256=manifest['program_sha256'],
                        source_sha256=sha(raw), source_all_positive=True,
                        source_boundary_false_positive_masks=summary['boundary_false_positive_masks'],
                        free_output_helper_sha256=RESCHEDULED_SHA,
                        scope='Candidate-only exact-target repair of an all-positive near-circuit; no exhaustion claim.')
            raw_cnf = helper.dimacs(cnf)
            meta['sha256'] = sha(raw_cnf)
            path = output / (name + '.cnf')
            path.write_bytes(raw_cnf)
            path.with_suffix('.json').write_text(json.dumps(meta, indent=2) + '\n')
            manifest['cases'].append({'case': name, **extra, 'variables': cnf.variables,
                'clauses': len(cnf.clauses), 'cnf_sha256': meta['sha256'],
                'metadata_sha256': sha(path.with_suffix('.json').read_bytes())})
    manifest['complete'] = True
    (output / 'family.json').write_text(json.dumps(manifest, indent=2) + '\n')
    return manifest


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--budgets', nargs='*', type=int, default=[2, 3])
    parser.add_argument('--local-counts', nargs='*', type=int, default=[3, 5])
    parser.add_argument('--max-false-positive-rows', type=int, default=15)
    parser.add_argument('--analysis-only', action='store_true')
    args = parser.parse_args()
    result = prepare(args.source, args.output, args.budgets, args.local_counts,
                     args.max_false_positive_rows, args.analysis_only)
    print(json.dumps({'family': str(args.output / 'family.json'), 'cases': len(result['cases']),
                      'analysis_only': result['analysis_only']}))
