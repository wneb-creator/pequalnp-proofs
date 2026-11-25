import argparse
import json
import time
from pathlib import Path

from global_synthesis import canonicalize, emit, evaluate
from incremental_cegis import Solver, model
from subset_cegis import stamp


def extend(mask):
    result = mask
    for i in range(3):
        for j in range(3):
            if mask >> (3 + i) & 1 or mask >> (6 + j) & 1:
                result |= 1 << (9 + 3 * i + j)
    return result


def target(mask):
    return bool((mask & 1 and mask & (4 + 8 + 16 + 32)) or
                (mask & 2 and mask & (4 + 64 + 128 + 256)))


def baseline(n):
    return [[1, 2, 3], [1, 4, n], [1, 5, n + 1], [0, 0, n + 2],
            [1, 2, 6], [1, 7, n + 4], [1, 8, n + 5], [0, 1, n + 6],
            [1, n + 3, n + 7]]


def approximate(n):
    return [[1, 0, 1], [1, 9, 13], [1, 17, n + 1], [1, 2, n + 2],
            [0, n, n + 3], [0, n + 4, n + 4],
            [0, n + 5, n + 5], [0, n + 6, n + 6]]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('output', type=Path)
    parser.add_argument('--seconds', type=int, default=60)
    args = parser.parse_args()
    n = 19  # Nine raw inputs, nine correlated cross-ORs, and free false.
    edges = [(0, 2), (0, 3), (0, 4), (0, 5),
             (1, 2), (1, 6), (1, 7), (1, 8)]
    negatives = [3, 449, 58, 508]
    raw_samples = [((1 << a) | (1 << b), 1) for a, b in edges]
    raw_samples += [(mask, 0) for mask in negatives]
    samples = [(extend(mask), label) for mask, label in raw_samples]
    for raw in range(512):
        if target(raw):
            assert any(label and mask & raw == mask for mask, label in raw_samples)
        else:
            assert any(not label and raw & mask == raw for mask, label in raw_samples)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'problem.json').write_text(json.dumps(dict(
        raw_inputs=9, available_inputs=n, gate_budget=8, tests=samples,
        target_edges=edges, maximal_negative_raw_masks=negatives)))
    for count, fixed in [(9, True), (8, False)]:
        folder = args.output / ('baseline9' if fixed else 'search8')
        folder.mkdir(exist_ok=True)
        hint = baseline(n) if fixed else approximate(n)
        hint = canonicalize(hint, n)
        path = folder / 'problem.cnf'
        selected, variables, clauses = emit(path, count, samples, ninputs=n,
            useful=False, fixed=hint if fixed else None, phase_seed=hint,
            order_max=True, order_lex=True, positive_live=True,
            negative_live=True, incomparable=True)
        solver = Solver(5821 + count)
        for op, sa, sb in selected:
            for lit in [op] + sa + sb:
                solver.freeze(lit)
        with path.open() as source:
            for line in source:
                if not line.startswith('p'):
                    solver.add(*[int(word) for word in line.split()[:-1]])
        # Every raw variable is directly indispensable even with all cross-ORs:
        # for ui, saturate all vj and set p=1,q=c=0; conversely for vj.
        # Every paid gate can be taken in the output cone, with copies for padding.
        required = list(range(9)) + list(range(n, n + count - 1))
        for wire in required:
            solver.add(*(side[wire] for i, (_, sa, sb) in enumerate(selected)
                         if wire < n + i for side in (sa, sb)))
        stamp('PAIR GADGET', count, 'gates', 'variables', variables, 'clauses', clauses,
              'required_raw_inputs', 9, 'free_features', 9)
        start = time.monotonic()
        result = solver.solve(10 if fixed else args.seconds)
        stamp('RESULT', count, result, 'seconds', round(time.monotonic() - start, 2))
        if fixed:
            assert result == 10
        if result == 10:
            answer = model(solver, selected)
            assert all(evaluate(answer, extend(raw), n) == target(raw) for raw in range(512))
            filename = 'BASELINE9.json' if fixed else 'EXACT8-GADGET.json'
            (args.output / filename).write_text(json.dumps(answer))
            stamp('VERIFIED ALL512 RAW INPUTS', count)
        solver.close()


if __name__ == '__main__':
    main()
