import argparse
import itertools
import json
import math
import random
import time
from pathlib import Path


def evaluate(n, gates, inputs):
    values = inputs[:]
    for op, a, b in gates:
        values.append(values[a] | values[b] if op else values[a] & values[b])
    return values[-1]


def star_seed(n, edges, rng):
    covers = []
    for size in range(n + 1):
        covers = [set(c) for c in itertools.combinations(range(n), size)
                  if all(a in c or b in c for a, b in edges)]
        if covers:
            break
    cover = rng.choice(covers)
    leaves = {v: [] for v in cover}
    for a, b in edges:
        possibilities = [v for v in (a, b) if v in cover]
        center = rng.choice(possibilities)
        leaves[center].append(b if center == a else a)
    gates = []
    terms = []
    centers = list(cover)
    rng.shuffle(centers)
    for center in centers:
        current = leaves[center][:]
        rng.shuffle(current)
        if not current:
            continue
        while len(current) > 1:
            a, b = current.pop(), current.pop()
            gates.append((1, a, b))
            current.append(n + len(gates) - 1)
        gates.append((0, center, current[0]))
        terms.append(n + len(gates) - 1)
    rng.shuffle(terms)
    while len(terms) > 1:
        a, b = terms.pop(), terms.pop()
        gates.append((1, a, b))
        terms.append(n + len(gates) - 1)
    return gates


def contract(n, gates, r, port):
    replacement = gates[r][port + 1]
    def remap(w):
        if w == n + r:
            w = replacement
        return w - 1 if w > n + r else w
    return [(op, remap(a), remap(b)) for i, (op, a, b) in enumerate(gates) if i != r]


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--encoding', required=True)
    p.add_argument('--seconds', type=int, default=600)
    p.add_argument('--seed', type=int, default=66)
    p.add_argument('--output', required=True)
    args = p.parse_args()
    data = json.loads(Path(args.encoding).read_text())
    n, edges = data['n'], data['edges']
    k = data['gate_count']
    tests = data['tests']
    inputs = [sum(((x >> i) & 1) << t for t, (x, _) in enumerate(tests)) for i in range(n)]
    target = sum(y << t for t, (_, y) in enumerate(tests))
    all_inputs = [sum(((x >> i) & 1) << x for x in range(1 << n)) for i in range(n)]
    full_target = sum(int(any((x >> a) & (x >> b) & 1 for a, b in edges)) << x
                      for x in range(1 << n))
    rng = random.Random(args.seed)
    start = time.monotonic()
    best = len(tests) + 1
    iterations = restarts = 0
    saved = None
    next_report = 0
    print(json.dumps({'event': 'start', 'n': n, 'gates': k, 'seconds': args.seconds,
                      'seed': args.seed, 'tests': len(tests)}), flush=True)
    while time.monotonic() - start < args.seconds:
        gates = star_seed(n, edges, rng)
        assert evaluate(n, gates, all_inputs) == full_target
        while len(gates) > k:
            gates = contract(n, gates, rng.randrange(len(gates) - 1), rng.randrange(2))
        if len(gates) != k:
            raise ValueError('unexpected seed gate count')
        score = (evaluate(n, gates, inputs) ^ target).bit_count()
        restarts += 1
        rounds = 20000
        for step in range(rounds + 1):
            iterations += 1
            if score < best:
                best = score
                saved = {'n': n, 'edges': edges, 'gate_count': k, 'gates': gates[:],
                         'test_errors': best, 'seed': args.seed, 'iterations': iterations,
                         'status': 'HEURISTIC_CANDIDATE_NOT_A_CORRECT_CIRCUIT'}
                if best == 0:
                    assert evaluate(n, gates, all_inputs) == full_target
                    saved['status'] = 'EXACT_TRUTH_TABLE_WITNESS_NOT_A_LOWER_BOUND'
                Path(args.output).write_text(json.dumps(saved, indent=2) + '\n')
                print(json.dumps({'event': 'best', 'errors': best, 'iterations': iterations,
                                  'elapsed': time.monotonic() - start}), flush=True)
                if best == 0:
                    return
            if iterations % 1000 == 0:
                elapsed = time.monotonic() - start
                if elapsed >= args.seconds:
                    break
                if elapsed >= next_report:
                    print(json.dumps({'event': 'progress', 'best': best, 'iterations': iterations,
                                      'restarts': restarts, 'elapsed': elapsed}), flush=True)
                    next_report = elapsed + 30
            if step == rounds:
                break
            index = rng.randrange(k)
            old = gates[index]
            op, a, b = old
            choice = rng.randrange(10)
            if choice == 0:
                op ^= 1
            elif choice < 5:
                a = rng.randrange(n + index)
            elif choice < 9:
                b = rng.randrange(n + index)
            else:
                op, a, b = rng.randrange(2), rng.randrange(n + index), rng.randrange(n + index)
            gates[index] = (op, a, b)
            trial = (evaluate(n, gates, inputs) ^ target).bit_count()
            temperature = 0.12 + 1.0 * (1 - step / rounds) ** 3
            if trial <= score or rng.random() < math.exp((score - trial) / temperature):
                score = trial
            else:
                gates[index] = old
    print(json.dumps({'event': 'finished', 'status': 'UNKNOWN', 'best_errors': best,
                      'iterations': iterations, 'restarts': restarts,
                      'elapsed': time.monotonic() - start}), flush=True)


if __name__ == '__main__':
    main()
