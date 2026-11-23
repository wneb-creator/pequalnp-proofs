import argparse
import functools
import itertools
import json
import math
import operator
import random
import time
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seconds', type=int, default=300)
    ap.add_argument('--seed', type=int, default=997)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    n, width = 14, 5
    y = {0, 1, 2}
    ps, qs, common = list(range(3, 8)), list(range(8, 13)), 13
    family = [{i, ps[j], qs[(j+i) % width]} for i in range(3) for j in range(width)]
    family += [set(ps + [common]), set(qs + [common])]
    factors = [0, 6, 12]
    prefix = []

    def add(op, a, b=None):
        prefix.append((op, a, b))
        return n + len(prefix) - 1

    factor_wires = []
    for f in factors:
        a, b, c = sorted(family[f])
        factor_wires.append(add('or', c, add('or', a, b)))
    h = add('and', factor_wires[0], factor_wires[1])
    h = add('and', h, factor_wires[2])
    z = add('not', h)
    ni = n + len(prefix)
    N = 1 << n
    universe = (1 << N) - 1
    fixed = []
    for p in range(n):
        b = 1 << p
        fixed.append((universe // ((1 << (2*b))-1)) * (((1 << b)-1) << b))
    for op, a, b in prefix:
        fixed.append((universe ^ fixed[a]) if op == 'not' else
                     (fixed[a] | fixed[b]) if op == 'or' else (fixed[a] & fixed[b]))
    target_bits = [functools.reduce(operator.or_, (fixed[p] for p in s), 0) for s in family]
    weights = [1 << len(s) for s in family]
    cache = {}

    def costs(bits):
        if bits not in cache:
            cache[bits] = tuple((bits ^ t).bit_count()*w for t, w in zip(target_bits, weights))
        return cache[bits]

    start_min = [min(costs(v)[j] for v in fixed) for j in range(len(family))]

    def evaluate(tail, detail=False):
        values = list(fixed)
        scores = list(start_min)
        for op, a, b in tail:
            bits = (values[a] | values[b]) if op == 'or' else (values[a] & values[b])
            values.append(bits)
            for j, c in enumerate(costs(bits)):
                if c < scores[j]:
                    scores[j] = c
        return (sum(scores), values, scores) if detail else sum(scores)

    tail_size = 28

    def baseline():
        tail = []
        for j, s in enumerate(family):
            if j in factors:
                continue
            ordered = list(s)
            rng.shuffle(ordered)
            acc = ordered[0]
            for p in ordered[1:]:
                tail.append(('or', acc, p))
                acc = ni + len(tail)-1
        while len(tail) > tail_size:
            removed = rng.randrange(len(tail))
            replacement = tail[removed][rng.choice([1, 2])]
            mapping = {j: j for j in range(ni)}
            reduced = []
            for j, (op, a, b) in enumerate(tail):
                if j == removed:
                    mapping[ni+j] = mapping[replacement]
                else:
                    reduced.append((op, mapping[a], mapping[b]))
                    mapping[ni+j] = ni+len(reduced)-1
            tail = reduced
        return tail

    started = time.monotonic()
    best_score = math.inf
    best = None
    total = 0
    restart = 0
    while time.monotonic()-started < args.seconds:
        tail = baseline()
        score = evaluate(tail)
        idle = 0
        for step in range(5000):
            if time.monotonic()-started >= args.seconds:
                break
            candidate = list(tail)
            for _ in range(rng.choices([1, 2, 3], [8, 2, 1])[0]):
                j = rng.randrange(tail_size)
                op, a, b = candidate[j]
                which = rng.randrange(5)
                if which == 0:
                    op = 'and' if op == 'or' else 'or'
                elif which <= 2:
                    a = rng.randrange(ni+j)
                else:
                    b = rng.randrange(ni+j)
                candidate[j] = (op, a, b)
            proposed = evaluate(candidate)
            total += 1
            if proposed <= score or rng.random() < math.exp(min(0, (score-proposed)/(N*.15))):
                tail, score = candidate, proposed
            if score < best_score:
                best_score, best = score, list(tail)
                print(json.dumps({'elapsed': time.monotonic()-started, 'restart': restart,
                                  'evaluations': total, 'best_normalized_error': score/N}), flush=True)
                result = {'n': n, 'family': [sorted(s) for s in family], 'y': sorted(y),
                          'prefix': prefix, 'tail': best, 'gates': len(prefix)+len(best),
                          'normalized_error': best_score/N, 'evaluations': total,
                          'elapsed': time.monotonic()-started}
                if score == 0:
                    _, values, _ = evaluate(best, True)
                    outputs = [values.index(t) for t in target_bits]
                    ym = sum(1 << p for p in y)
                    disjoint = [s for s in family if not s & y]
                    refunds = []
                    for index, bits in enumerate(values[n:]):
                        light = {p for p in range(n) if (bits >> (1 << p)) & 1}
                        heavy = {p for p in range(n) if p not in y and (bits >> (ym | (1 << p))) & 1}
                        if light in family and heavy in disjoint:
                            refunds.append(index)
                    lhs = sum(len(s) if not s & y else min(3, len(s)) for s in family)
                    rhs = len(prefix)+len(best)+len(refunds)+len(family)
                    result.update({'outputs': outputs, 'refunds': refunds, 'lhs': lhs,
                                   'rhs': rhs, 'actual_counterexample': lhs > rhs})
                    args.output.write_text(json.dumps(result, indent=2))
                    print(json.dumps(result), flush=True)
                    return
                args.output.write_text(json.dumps(result, indent=2))
                idle = 0
            else:
                idle += 1
            if idle > 2000:
                break
            if len(cache) > 30000:
                cache.clear()
        restart += 1
    result = json.loads(args.output.read_text())
    result.update({'completed': True, 'evaluations_total': total,
                   'elapsed_total': time.monotonic()-started, 'restarts': restart})
    args.output.write_text(json.dumps(result, indent=2))
    print(json.dumps({k: v for k, v in result.items() if k not in ['prefix', 'tail', 'family']}), flush=True)


if __name__ == '__main__':
    main()
