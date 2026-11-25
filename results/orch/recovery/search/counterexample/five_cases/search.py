"""Prepare/run one Petersen sole-NOT orbit case, or the separate monotone<=18 case.

No UNSAT result from this program is a Lean proof. Every SAT model is independently
checked on all 1024 inputs before a computational witness is written. See README.md.
"""
import argparse
import json
from pathlib import Path
import random
import sys
import time

Z3_PYTHON = '/tmp/oec/pequalnp-pilot-109/counterexample/z3-5.3.3-x64-glibc-2.39/bin/python'
EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
         (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
CASES = [(50, 3), (50, 6), (50, 12), (116, 3), (116, 6)]


def target(mask):
    return any(bool(mask & (1 << i)) and bool(mask & (1 << j)) for i, j in EDGES)


def maximal_independent(mask):
    return not target(mask) and all(target(mask | (1 << i))
                                   for i in range(10) if not mask & (1 << i))


def evaluate(gates, mask, output=None, forced_not=None):
    wires = [bool(mask & (1 << i)) for i in range(10)]
    for op, a, b in gates:
        if op == 0:
            wires.append(wires[a] and wires[b])
        elif op == 1:
            wires.append(wires[a] or wires[b])
        elif op == 2:
            wires.append(not wires[a] if forced_not is None else forced_not)
        else:
            raise ValueError('invalid operation')
    return wires[-1 if output is None else output]


def validate_shape(gates, expected_nots):
    assert sum(op == 2 for op, _, _ in gates) == expected_nots
    for g, (op, a, b) in enumerate(gates):
        assert op in (0, 1, 2)
        assert 0 <= a < 10 + g and 0 <= b < 10 + g
        assert op != 2 or a == b


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--case', type=int, choices=range(5))
    mode.add_argument('--monotone18', action='store_true')
    parser.add_argument('--rows', choices=['boundary', '91', 'dense', 'full'], default='boundary')
    parser.add_argument('--budget-seconds', type=float, default=600)
    parser.add_argument('--seed', type=int, default=109)
    parser.add_argument('--essential-at-pair', action='store_true')
    parser.add_argument('--normalize-not', action='store_true')
    parser.add_argument('--strict-binary', action='store_true',
                        help='exclude identity padding; a heuristic extra restriction')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--dry-run', action='store_true', help='check static case data; do not invoke SMT')
    args = parser.parse_args()
    if args.budget_seconds <= 0:
        parser.error('budget must be positive')
    if args.monotone18 and (args.essential_at_pair or args.normalize_not):
        parser.error('sole-NOT flags do not apply to monotone18')
    for independent, edge in CASES:
        assert maximal_independent(independent)
        assert edge.bit_count() == 2 and target(edge)
    pair = CASES[args.case] if args.case is not None else None
    gate_count, not_count = (18, 0) if args.monotone18 else (19, 1)
    if args.rows == 'full':
        initial_rows = list(range(1024))
    elif args.rows == 'boundary':
        initial_rows = [x for x in range(1024) if maximal_independent(x)
                        or (x.bit_count() == 2 and target(x))]
    elif args.rows == '91':
        initial_rows = [x for x in range(1024) if not target(x) or x.bit_count() == 2]
    else:
        initial_rows = [x for x in range(1024) if not target(x) or x.bit_count() in (2, 3, 9, 10)]
    if pair:
        assert all(x in initial_rows for x in pair)
    metadata = {'case': args.case, 'pair': pair, 'gates': gate_count, 'nots': not_count,
                'initial_rows': len(initial_rows), 'budget_seconds': args.budget_seconds,
                'essential_at_pair': args.essential_at_pair,
                'normalize_not': args.normalize_not, 'strict_binary': args.strict_binary}
    print('PREPARED', json.dumps(metadata), flush=True)
    if args.dry_run:
        return

    sys.path.insert(0, Z3_PYTHON)
    import z3
    started = time.monotonic()
    solver = z3.SolverFor('QF_BV')
    solver.set(random_seed=args.seed)
    ops = [z3.BitVec('op%d' % g, 2) for g in range(gate_count)]
    aa = [z3.BitVec('a%d' % g, 5) for g in range(gate_count)]
    bb = [z3.BitVec('b%d' % g, 5) for g in range(gate_count)]
    for g in range(gate_count):
        solver.add(z3.ULE(ops[g], 2), z3.ULT(aa[g], 10 + g), z3.ULT(bb[g], 10 + g))
        order = z3.ULT(aa[g], bb[g]) if args.strict_binary else z3.ULE(aa[g], bb[g])
        solver.add(z3.If(ops[g] == 2, aa[g] == bb[g], order))
    solver.add(sum([z3.If(op == 2, z3.BitVecVal(1, 5), z3.BitVecVal(0, 5))
                    for op in ops], z3.BitVecVal(0, 5)) == not_count)
    # Every input and every nonoutput gate has a syntactic use.
    for wire in range(10 + gate_count - 1):
        uses = [z3.Or(aa[g] == wire, z3.And(ops[g] != 2, bb[g] == wire))
                for g in range(gate_count) if wire < 10 + g]
        solver.add(z3.Or(*uses))
    for g in range(gate_count - 1):
        independent = z3.And(aa[g + 1] != 10 + g, bb[g + 1] != 10 + g)
        solver.add(z3.Implies(z3.And(ops[g] == ops[g + 1], independent),
                              z3.ULE(aa[g], aa[g + 1])))
    if args.normalize_not:
        for g in range(1, gate_count):
            solver.add(z3.Implies(ops[g] == 2, aa[g] == 9 + g))

    def trace(rows, tag, forced_not=None):
        width = len(rows)
        wires = [z3.BitVecVal(sum(((x >> i) & 1) << k for k, x in enumerate(rows)), width)
                 for i in range(10)]
        operands = []
        for g in range(gate_count):
            def pick(selector):
                value = wires[-1]
                for j in range(len(wires) - 2, -1, -1):
                    value = z3.If(selector == j, wires[j], value)
                return value
            va, vb = pick(aa[g]), pick(bb[g])
            inverted = ~va if forced_not is None else z3.BitVecVal(
                (1 << width) - 1 if forced_not else 0, width)
            output = z3.BitVec('%s_v%d' % (tag, g), width)
            solver.add(output == z3.If(ops[g] == 0, va & vb,
                                      z3.If(ops[g] == 1, va | vb, inverted)))
            operands.append(va)
            wires.append(output)
        return wires[-1], operands

    seen = set()
    batch = 0

    def add_samples(rows):
        nonlocal batch
        rows = [x for x in rows if x not in seen]
        if not rows:
            return
        seen.update(rows)
        output, operands = trace(rows, 'rows%d' % batch)
        wanted = sum(int(target(x)) << k for k, x in enumerate(rows))
        solver.add(output == z3.BitVecVal(wanted, len(rows)))
        if batch == 0 and pair:
            im, ie = rows.index(pair[0]), rows.index(pair[1])
            for g, operand in enumerate(operands):
                solver.add(z3.Implies(ops[g] == 2,
                    z3.And(z3.Extract(im, im, operand) == 1,
                           z3.Extract(ie, ie, operand) == 0)))
        batch += 1

    add_samples(initial_rows)
    if args.essential_at_pair:
        forced_true, _ = trace([pair[0]], 'forced_true', True)
        forced_false, _ = trace([pair[1]], 'forced_false', False)
        solver.add(forced_true == 1, forced_false == 0)
    print('START', time.time(), flush=True)
    for iteration in range(100):
        remaining = args.budget_seconds - (time.monotonic() - started)
        if remaining <= 0:
            print('UNKNOWN global wall budget expired', flush=True)
            break
        solver.set(timeout=max(1, int(remaining * 1000)))
        before = time.monotonic()
        verdict = solver.check()
        print('CHECK', iteration, str(verdict), 'seconds', time.monotonic() - before,
              'samples', len(seen), flush=True)
        if verdict != z3.sat:
            print('REASON', solver.reason_unknown() if verdict == z3.unknown
                  else 'UNSAT for this search encoding only; no Lean certificate', flush=True)
            print(solver.statistics(), flush=True)
            break
        model = solver.model()
        gates = [[model.eval(ops[g]).as_long(), model.eval(aa[g]).as_long(),
                  model.eval(bb[g]).as_long()] for g in range(gate_count)]
        validate_shape(gates, not_count)
        bad = [x for x in range(1024) if evaluate(gates, x) != target(x)]
        print('CANDIDATE', json.dumps(gates), 'errors', len(bad), flush=True)
        if bad:
            random.Random(args.seed + iteration).shuffle(bad)
            add_samples(bad[:64])
            continue
        original_gates = gates
        output_wire = 10 + gate_count - 1
        if args.monotone18:
            gates = gates + [[2, 0, 0]]  # A dead NOT preserves the old output wire.
        validate_shape(gates, 1)
        assert len(gates) <= 19
        assert all(evaluate(gates, x, output_wire) == target(x) for x in range(1024))
        essential = {'forcing_true_changes_output': any(
                         evaluate(gates, x, output_wire, True) != target(x) for x in range(1024)),
                     'forcing_false_changes_output': any(
                         evaluate(gates, x, output_wire, False) != target(x) for x in range(1024))}
        if pair:
            not_index = next(g for g, (op, _, _) in enumerate(original_gates) if op == 2)
            source = original_gates[not_index][1]
            assert evaluate(original_gates[:not_index], pair[0], source)
            assert not evaluate(original_gates[:not_index], pair[1], source)
        result = {'gates': gates, 'output': output_wire, 'case': args.case, 'pair': pair,
                  'verification': 'independent Python evaluation on all 1024 inputs; not Lean checked',
                  'essentiality': essential}
        args.output.write_text(json.dumps(result, indent=2) + '\n')
        print('WITNESS', json.dumps(result), flush=True)
        break


if __name__ == '__main__':
    main()
