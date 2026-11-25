import argparse
import json
import time
from pathlib import Path

from global_synthesis import canonicalize, emit, evaluate
from incremental_cegis import LiveCNF, Solver, model
from subset_cegis import stamp


def extend(case, mask):
    answer = mask
    for i, feature in enumerate(case['features']):
        if any(mask >> j & 1 for j in feature['raw_indices']):
            answer |= 1 << (case['raw_inputs'] + i)
    return answer


def target(case, mask):
    return any(mask >> a & 1 and mask >> b & 1 for a, b in case['edges'])


def star_seed(case, merge=False):
    n = case['inputs']
    gates = []

    def gate(op, a, b):
        gates.append([op, min(a, b), max(a, b)])
        return n + len(gates) - 1

    def disj(wires):
        answer, *rest = sorted(wires)
        for wire in rest:
            answer = gate(1, answer, wire)
        return answer

    owners = sorted(set(a for a, _ in case['edges']))
    groups = [owners[:2]] + [[owner] for owner in owners[2:]] if merge else [[x] for x in owners]
    terms = []
    for group in groups:
        points = disj(group)
        lines = disj(set(b for a, b in case['edges'] if a in group))
        terms.append(gate(0, points, lines))
    disj(terms)
    return canonicalize(gates, n)


def verify_problem(case):
    r = case['raw_inputs']
    assert case['inputs'] == r + len(case['features'])
    assert case['tests'] == [[extend(case, mask), label] for mask, label in case['raw_tests']]
    assert all(target(case, mask) == bool(label) for mask, label in case['raw_tests'])
    negative_masks = [mask for mask, label in case['raw_tests'] if not label]
    assert len(set(negative_masks)) == len(negative_masks)
    truths = [target(case, mask) for mask in range(1 << r)]
    extensions = [extend(case, mask) for mask in range(1 << r)]
    for raw, expected in enumerate(truths):
        if expected:
            assert any(label and mask & raw == mask for mask, label in case['raw_tests'])
        else:
            assert any(not label and raw & mask == raw for mask, label in case['raw_tests'])
    witnesses = []
    for i in range(r):
        witness = next((raw for raw in range(1 << r) if not (raw >> i & 1)
                        and truths[raw] != truths[raw | (1 << i)]
                        and extensions[raw] ^ extensions[raw | (1 << i)] == 1 << i), None)
        assert witness is not None, ('raw input not directly indispensable', i)
        witnesses.append([i, witness, witness | (1 << i)])
    return witnesses


def support_constraints(cnf, selected, n, raw_inputs):
    count = len(selected)
    excess = count - raw_inputs + 1
    assert excess >= 0
    extras = []
    required = list(range(raw_inputs)) + list(range(n, n + count - 1))
    for wire in required:
        occurrences = [side[wire] for i, (_, sa, sb) in enumerate(selected)
                       if wire < n + i for side in (sa, sb)]
        cnf.clause(*occurrences)
        levels = cnf.count_row(occurrences, excess + 1)
        cnf.clause(-levels[excess + 2])
        extras.extend(levels[2:excess + 2])
    for _, sa, sb in selected:
        for side in (sa, sb):
            feature_selectors = side[raw_inputs:n]
            uses_feature = cnf.var()
            cnf.clause(-uses_feature, *feature_selectors)
            for selector in feature_selectors:
                cnf.clause(-selector, uses_feature)
            extras.append(uses_feature)
    levels = cnf.count_row(extras, excess)
    cnf.clause(-levels[excess + 1])
    return excess


def assemble(case, answer):
    gates = [list(gate) for gate in case['outside_gates']]
    mapping = case['input_original'] + [feature['outside_wire'] for feature in case['features']]
    assert len(mapping) == case['inputs']
    for op, a, b in answer:
        assert a < len(mapping) and b < len(mapping)
        gates.append([op, mapping[a], mapping[b]])
        mapping.append(26 + len(gates) - 1)
    gates.append([1, case['outside_output'], mapping[-1]])
    assert len(gates) == case['total_if_target_met'] <= 63
    return gates


def run(case, folder, seconds, seed, fixed=False, excess=True, phase_seed=None,
        crossings=False, zero_wildcards=False, kraft=False, and_count=None):
    folder.mkdir(parents=True, exist_ok=True)
    n = case['inputs']
    hint = star_seed(case, not fixed) if fixed or phase_seed is None else [list(g) for g in phase_seed]
    count = len(hint) if fixed else case['max_gates']
    while len(hint) < count:
        output = n + len(hint) - 1
        hint.append([0, output, output])
    hint = canonicalize(hint, n)
    assert len(hint) == count
    negatives = [i for i, (_, label) in enumerate(case['tests']) if not label]
    join_pairs = []
    for position, left in enumerate(negatives):
        for right in negatives[position + 1:]:
            raw_left = case['raw_tests'][left][0]
            raw_right = case['raw_tests'][right][0]
            assert target(case, raw_left | raw_right)
            assert extend(case, raw_left | raw_right) == case['tests'][left][0] | case['tests'][right][0]
            join_pairs.append((left, right))
    minimum_ands = (len(negatives) - 1).bit_length()
    assert not zero_wildcards or len(negatives) == 1 << minimum_ands
    path = folder / 'problem.cnf'
    selected, variables, clauses = emit(path, count, case['tests'], ninputs=n,
        useful=False, fixed=hint if fixed else None, phase_seed=hint,
        order_max=True, order_lex=True, positive_live=True,
        negative_live=True, incomparable=True,
        negative_join_pairs=join_pairs if crossings else None,
        zero_wildcard_and_limit=minimum_ands if zero_wildcards else None,
        kraft_linear_and_limit=minimum_ands if kraft else None,
        and_count=and_count if not fixed else None)
    solver = Solver(seed)
    for op, sa, sb in selected:
        for literal in [op] + sa + sb:
            solver.freeze(literal)
    with path.open() as source:
        for line in source:
            if not line.startswith('p'):
                solver.add(*[int(word) for word in line.split()[:-1]])
    with (folder / 'support-clauses.cnfpart').open('w') as journal:
        cnf = LiveCNF(solver, variables, clauses, journal)
        and_levels = cnf.count_row([-op for op, _, _ in selected], minimum_ands)
        cnf.clause(and_levels[minimum_ands])
        if excess:
            allowance = support_constraints(cnf, selected, n, case['raw_inputs'])
        else:
            allowance = None
        stamp('FEATURE GADGET', case['name'], count, 'gates',
              'variables', cnf.variables, 'clauses', cnf.clauses,
              'raw', case['raw_inputs'], 'features', len(case['features']), 'excess', allowance,
              'minimum_ands', minimum_ands, 'join_crossings', crossings)
        journal.flush()
        start = time.monotonic()
        result = solver.solve(20 if fixed else seconds)
        elapsed = round(time.monotonic() - start, 2)
        stamp('RESULT', case['name'], count, result, 'seconds', elapsed)
        report = dict(case=case['name'], gates=count, result=result, seconds=elapsed,
                      variables=cnf.variables, clauses=cnf.clauses, fixed=fixed,
                      fixed_and_count=and_count if not fixed else None,
                      crossing_cuts=crossings, kraft_linear_cut=kraft,
                      zero_wildcard_cut=zero_wildcards)
        if fixed:
            assert result == 10, report
        if result == 10:
            answer = model(solver, selected)
            assert all(evaluate(answer, extend(case, raw), n) == target(case, raw)
                       for raw in range(1 << case['raw_inputs']))
            report['gates_list'] = answer
            report['all_raw_assignments_checked'] = 1 << case['raw_inputs']
            stamp('VERIFIED ALL RAW INPUTS', case['name'], 1 << case['raw_inputs'])
            if not fixed:
                report['sufficient_for_full63'] = 'outside_gates' in case
                if 'outside_gates' in case:
                    report['full_circuit'] = assemble(case, answer)
                    geometry_path = Path(__file__).resolve().parents[2] / 'circuit_search' / 'geometry.json'
                    geometry = json.loads(geometry_path.read_text())
                    full_tests = [((1 << a) | (1 << b), True) for a, b in geometry['edges']]
                    full_tests += [(points | (lines << 13), False)
                                   for points, lines in geometry['maximal_independent_sets']]
                    assert all(evaluate(report['full_circuit'], mask, 26) == label
                               for mask, label in full_tests)
                    report['full_boundary_tests_checked'] = len(full_tests)
                (folder / 'EXACT-GADGET.json').write_text(json.dumps(report))
        (folder / 'result.json').write_text(json.dumps(report))
    solver.close()
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('pack', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--cases', default='0')
    parser.add_argument('--seconds', type=int, default=90)
    parser.add_argument('--seed', type=int, default=57300)
    parser.add_argument('--phase-file', type=Path)
    parser.add_argument('--phase-index', type=int, default=0)
    parser.add_argument('--crossings', action='store_true')
    parser.add_argument('--zero-wildcards', action='store_true')
    parser.add_argument('--kraft', action='store_true')
    parser.add_argument('--and-count', type=int)
    args = parser.parse_args()
    pack = json.loads(args.pack.read_text())
    if isinstance(pack, dict):
        pack = [pack]
    phase_seed = None
    if args.phase_file:
        phase_data = json.loads(args.phase_file.read_text())
        phase_seed = phase_data[args.phase_index]['gates']
    args.output.mkdir(parents=True, exist_ok=True)
    for index in map(int, args.cases.split(',')):
        case = pack[index]
        folder = args.output / case['name']
        folder.mkdir(parents=True, exist_ok=True)
        witnesses = verify_problem(case)
        (folder / 'problem.json').write_text(json.dumps(case))
        (folder / 'direct-essential-witnesses.json').write_text(json.dumps(witnesses))
        stamp('VERIFIED BASIS AND DIRECT ESSENTIALITY', case['name'], len(witnesses))
        run(case, folder / 'baseline', 20, args.seed + index, fixed=True,
            crossings=args.crossings, zero_wildcards=args.zero_wildcards, kraft=args.kraft)
        result = run(case, folder / 'search', args.seconds, args.seed + 100 + index,
                     phase_seed=phase_seed, crossings=args.crossings,
                     zero_wildcards=args.zero_wildcards, kraft=args.kraft,
                     and_count=args.and_count)
        if result == 10:
            break


if __name__ == '__main__':
    main()
