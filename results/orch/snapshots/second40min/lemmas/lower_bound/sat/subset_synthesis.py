import argparse
import json
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path

from global_synthesis import CADICAL, canonicalize, emit, evaluate, read_model


def main():
    p = argparse.ArgumentParser()
    p.add_argument('problem', type=Path)
    p.add_argument('output', type=Path)
    p.add_argument('--seconds', type=int, default=600)
    p.add_argument('--seed', type=int, default=5703)
    p.add_argument('--plain-order', action='store_true')
    p.add_argument('--gates', type=int)
    p.add_argument('--lex', action='store_true')
    p.add_argument('--ands', type=int)
    p.add_argument('--last-and', action='store_true')
    p.add_argument('--positive-live', action='store_true')
    p.add_argument('--first', nargs=3, type=int)
    p.add_argument('--incomparable', action='store_true')
    p.add_argument('--dominance', action='store_true')
    p.add_argument('--negative-live', action='store_true')
    p.add_argument('--wire-excess', action='store_true')
    p.add_argument('--phase-seed', type=Path)
    args = p.parse_args()
    data = json.loads(args.problem.read_text())
    n = data['inputs']
    count = args.gates or data['max_gates']
    samples = data['tests']
    edges = data['edges']
    for mask, value in samples:
        assert any((mask >> a & 1) and (mask >> b & 1) for a, b in edges) == bool(value)
    negative = [mask for mask, label in samples if not label]
    left_n = len(data['original_rows'])
    for left in range(1 << left_n):
        right = sum(1 << j for j in range(left_n, n)
                    if not any(a < left_n and b == j and (left >> a & 1) for a, b in edges))
        assert any((left | right) & ~mask == 0 for mask in negative)
    assert all(evaluate(data['seed']['gates'], mask, n) == bool(label) for mask, label in samples)
    args.output.mkdir(parents=True, exist_ok=True)
    phase_seed = None
    if args.phase_seed:
        phase_data = json.loads(args.phase_seed.read_text())
        phase_seed = phase_data['gates'] if isinstance(phase_data, dict) else phase_data
        assert len(phase_seed) == count
        phase_seed = [[op, *sorted((a, b))] for op, a, b in phase_seed]
        if not args.plain_order or args.lex:
            phase_seed = canonicalize(phase_seed, n)
    begin = time.monotonic()
    path = args.output / 'problem.cnf'
    selected, nvars, nclauses = emit(path, count, samples, ninputs=n,
                                    order_max=not args.plain_order, order_lex=args.lex,
                                    and_count=args.ands, last_and=args.last_and,
                                    positive_live=args.positive_live, first=args.first,
                                    incomparable=args.incomparable, dominance=args.dominance,
                                    negative_live=args.negative_live, wire_excess=args.wire_excess,
                                    phase_seed=phase_seed)
    print(datetime.now(timezone.utc).isoformat(), data['name'], 'inputs', n, 'gates', count,
          'samples', len(samples), 'variables', nvars, 'clauses', nclauses,
          'generation_seconds', round(time.monotonic() - begin, 2), flush=True)
    solution = args.output / 'solution.txt'
    with (args.output / 'solver.log').open('w') as log:
        result = subprocess.run([CADICAL, '-t', str(args.seconds), '--seed=' + str(args.seed),
                                 '-w', str(solution), str(path)],
                                stdout=log, stderr=subprocess.STDOUT)
    print(datetime.now(timezone.utc).isoformat(), 'RESULT', result.returncode,
          'elapsed', round(time.monotonic() - begin, 2), flush=True)
    if result.returncode != 10:
        return
    answer = read_model(solution, selected)
    assert all(evaluate(answer, mask, n) == bool(value) for mask, value in samples)
    meets_target = len(answer) <= data['max_gates']
    filename = 'EXACT-WITNESS.json' if meets_target else 'BASELINE-WITNESS.json'
    (args.output / filename).write_text(json.dumps(answer))
    print('EXACT FUNCTION WITNESS', len(answer), 'gates;',
          'MEETS TARGET' if meets_target else 'EXCEEDS TARGET', data['max_gates'], flush=True)


if __name__ == '__main__':
    main()
