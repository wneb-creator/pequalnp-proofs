import argparse
import json
import random
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path

from global_synthesis import CADICAL, canonicalize, emit, evaluate, read_model


def stamp(*args):
    print(datetime.now(timezone.utc).isoformat(), *args, flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('problem', type=Path)
    parser.add_argument('seeds', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--index', type=int, default=15)
    parser.add_argument('--seconds', type=int, default=120)
    parser.add_argument('--rounds', type=int, default=30)
    parser.add_argument('--add', type=int, default=4)
    parser.add_argument('--seed', type=int, default=5791)
    parser.add_argument('--all-pairs', action='store_true')
    args = parser.parse_args()
    data = json.loads(args.problem.read_text())
    pack = json.loads(args.seeds.read_text())
    start = pack[args.index]
    n, count = data['inputs'], data['max_gates']
    answer = start['gates']
    answer = [[op, *sorted((a, b))] for op, a, b in answer]
    while len(answer) < count:
        last = n + len(answer) - 1
        answer.append([0, last, last])
    assert len(answer) == count
    answer = canonicalize(answer, n)
    samples = [(mask, label) for mask, label in data['tests'] if label]
    samples += [(0, 0)] + [(1 << i, 0) for i in range(n)]
    if args.all_pairs:
        for a in range(n):
            for b in range(a):
                mask = (1 << a) | (1 << b)
                label = int(any(mask >> u & 1 and mask >> v & 1 for u, v in data['edges']))
                samples.append((mask, label))
    samples = list(dict.fromkeys(samples))
    known = {mask for mask, _ in samples}
    rng = random.Random(args.seed)
    args.output.mkdir(parents=True, exist_ok=True)
    stamp('START', start.get('group'), 'gates', count, 'samples', len(samples))
    for round_no in range(args.rounds):
        wrong = [(mask, label) for mask, label in data['tests']
                 if evaluate(answer, mask, n) != bool(label)]
        stamp('CANDIDATE', round_no, 'errors', len(wrong))
        (args.output / f'candidate-{round_no}.json').write_text(json.dumps(answer))
        if not wrong:
            (args.output / 'EXACT-WITNESS.json').write_text(json.dumps(answer))
            stamp('EXACT TARGET WITNESS', len(answer))
            return
        minimized = set()
        for mask, label in wrong:
            assert not label
            order = list(range(n))
            rng.shuffle(order)
            for j in order:
                small = mask & ~(1 << j)
                if evaluate(answer, small, n):
                    mask = small
            assert not any(mask >> u & 1 and mask >> v & 1 for u, v in data['edges'])
            if mask not in known:
                minimized.add(mask)
        assert minimized
        chosen = sorted(minimized, key=lambda mask: (mask.bit_count(), mask))[:args.add]
        stamp('ADD', [(mask, mask.bit_count()) for mask in chosen], 'available', len(minimized))
        samples.extend((mask, 0) for mask in chosen)
        known.update(chosen)
        folder = args.output / f'round-{round_no}'
        folder.mkdir(exist_ok=True)
        (folder / 'samples.json').write_text(json.dumps(samples))
        begin = time.monotonic()
        selected, nvars, nclauses = emit(folder / 'problem.cnf', count, samples, ninputs=n,
                                       order_max=True, order_lex=True, positive_live=True,
                                       phase_seed=canonicalize(answer, n))
        stamp('ENCODING', round_no, 'samples', len(samples), 'variables', nvars,
              'clauses', nclauses, 'seconds', round(time.monotonic() - begin, 2))
        solution = folder / 'solution.txt'
        with (folder / 'solver.log').open('w') as log:
            result = subprocess.run([CADICAL, '-t', str(args.seconds),
                                     '--seed=' + str(args.seed + round_no),
                                     '-w', str(solution), str(folder / 'problem.cnf')],
                                    stdout=log, stderr=subprocess.STDOUT)
        stamp('SOLVER', result.returncode, 'seconds', round(time.monotonic() - begin, 2))
        if result.returncode != 10:
            return
        answer = read_model(solution, selected)
        assert all(evaluate(answer, mask, n) == bool(label) for mask, label in samples)


if __name__ == '__main__':
    main()
