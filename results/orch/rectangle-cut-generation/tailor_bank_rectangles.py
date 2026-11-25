import argparse
import hashlib
import json
import math
import time
from collections import Counter
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

BASE = Path(__file__).resolve().parent
EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
         (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
POSITIVE = [(1 << a) | (1 << b) for a, b in EDGES]
INDEPENDENT = [r for r in range(1024)
               if not any((r >> a) & 1 and (r >> b) & 1 for a, b in EDGES)]
NEGATIVE = [r for r in INDEPENDENT
            if all((r >> i) & 1 or (r | (1 << i)) not in INDEPENDENT for i in range(10))]


def profile(g):
    return (tuple(i for i, r in enumerate(POSITIVE) if (g >> r) & 1),
            tuple(i for i, r in enumerate(NEGATIVE) if not ((g >> r) & 1)))


class Oracle:
    def __init__(self, ps, ns):
        self.ps, self.ns = ps, ns
        self.transpose = len(ns) < len(ps)
        self.small = ns if self.transpose else ps
        self.large = ps if self.transpose else ns
        self.masks = ((np.arange(1 << len(self.small), dtype=np.uint32)[:, None]
                       >> np.arange(len(self.small), dtype=np.uint32)) & 1).astype(np.int64)

    def values(self, weights):
        a = weights[np.ix_(self.ps, self.ns)]
        if self.transpose:
            a = a.T
        sums = self.masks @ a
        return np.maximum(sums, 0).sum(axis=1), sums

    def maximum(self, weights):
        values, _ = self.values(weights)
        return int(values.max())

    def witnesses(self, weights, cap, count=4):
        values, sums = self.values(weights)
        ix = np.flatnonzero(values > cap + 1e-7)
        if len(ix) > count:
            ix = ix[np.argpartition(values[ix], -count)[-count:]]
        out = []
        for i in ix:
            small = tuple(a for a, bit in zip(self.small, self.masks[i]) if bit)
            large = tuple(a for a, v in zip(self.large, sums[i]) if v > 1e-9)
            out.append((large, small) if self.transpose else (small, large))
        return out


def normalize(weights):
    d = math.gcd(*(abs(int(x)) for x in weights.flat))
    return weights // max(d, 1)


def rational_candidates(weights):
    seen = set()
    fractions = [Fraction(float(x)).limit_denominator(512) for x in weights.flat]
    denominator = math.lcm(*(x.denominator for x in fractions))
    candidates = []
    if denominator <= 65536:
        candidates.append(np.array([x.numerator * (denominator // x.denominator)
                                    for x in fractions], dtype=np.int64).reshape(weights.shape))
    for scale in [1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 24, 32, 48, 64, 96,
                  128, 192, 256, 512, 1024, 4096, 16384]:
        candidates.append(np.rint(weights * scale).astype(np.int64))
    candidates.sort(key=lambda x: (int(np.abs(x).max()), sum(abs(int(v)) for v in x.flat)))
    for candidate in candidates:
        candidate = normalize(candidate)
        key = tuple(int(v) for v in candidate.flat)
        if key not in seen:
            seen.add(key)
            yield candidate


def solve(bank, seconds, iterations, output, prefix, minimum_gap=0.):
    roots = [int(x, 16) for x in bank['state']]
    assert bank['remaining'] == len(roots) - 1
    profiles = [profile(g) for g in roots]
    multiplicities = Counter(profiles)
    unique = list(multiplicities)
    oracle = [Oracle(*pr) for pr in unique]
    counts = np.array([multiplicities[pr] for pr in unique], dtype=np.int64)
    p, n, m = len(POSITIVE), len(NEGATIVE), len(unique)
    rects, seen = [], set()

    def add(gid, ps, ns):
        key = (gid, ps, ns)
        if not ps or not ns or key in seen:
            return
        seen.add(key)
        row = np.zeros(p * n + m)
        row[p * n + gid] = -1
        for r in ps:
            for c in ns:
                row[r * n + c] = 1
        rects.append(row)

    for i, (ps, ns) in enumerate(unique):
        add(i, ps, ns)
    start = time.monotonic()
    objective = np.r_[-np.ones(p * n), counts]
    last_valid = None
    for it in range(iterations):
        sol = linprog(objective, A_ub=csr_matrix(np.array(rects)),
                      b_ub=np.zeros(len(rects)),
                      bounds=[(-10., 1.)] * (p * n) + [(0., 1.)] * m,
                      method='highs', options={'time_limit': max(1., seconds - (time.monotonic() - start))})
        if not sol.success:
            return {'node': bank['node'], 'status': 'solver_error', 'message': sol.message,
                    'seconds': time.monotonic() - start, 'iterations': it}
        weights, costs = sol.x[:p * n].reshape((p, n)), sol.x[p * n:]
        violated = []
        maxima = []
        for i, o in enumerate(oracle):
            values, _ = o.values(weights)
            maxima.append(float(values.max()))
            violated.extend((i, ps, ns) for ps, ns in o.witnesses(weights, costs[i]))
        valid = float(weights.sum() - counts @ np.array(maxima))
        last_valid = valid
        if it % 5 == 0 or valid > 1e-7 or not violated:
            print(json.dumps({'node': bank['node'], 'iteration': it, 'lp_gap': -float(sol.fun),
                              'valid_float_gap': valid, 'constraints': len(rects),
                              'seconds': time.monotonic() - start}), flush=True)
        if valid > max(1e-7, minimum_gap) or (valid > 1e-7 and not violated):
            for integer_weights in rational_candidates(weights):
                exact = [o.maximum(integer_weights) for o in oracle]
                total = sum(int(v) for v in integer_weights.flat)
                cost_sum = sum(int(c) * int(v) for c, v in zip(counts, exact))
                if total <= cost_sum:
                    continue
                lookup = dict(zip(unique, exact))
                root_costs = [lookup[pr] for pr in profiles]
                result = {
                    'name': f'{prefix}{bank["node"]}', 'source_bank': bank['node'],
                    'positive_rows': POSITIVE, 'negative_rows': NEGATIVE,
                    'weights': integer_weights.tolist(), 'total': total,
                    'state': bank['state'], 'remaining': bank['remaining'],
                    'root_costs': root_costs, 'cost_sum': cost_sum, 'margin': total - cost_sum,
                    'profile_count': m, 'iterations': it + 1,
                    'seconds': time.monotonic() - start,
                    'exact_validation': 'Integer subset enumeration; independent audit pending',
                    'source_bank_sha256': hashlib.sha256(json.dumps(bank, sort_keys=True).encode()).hexdigest(),
                }
                filename = output / f'{prefix}{bank["node"]}.json'
                assert not filename.exists(), filename
                filename.write_text(json.dumps(result, indent=2) + '\n')
                print(json.dumps({'node': bank['node'], 'status': 'exact_separation',
                                  'total': total, 'cost_sum': cost_sum, 'margin': total - cost_sum,
                                  'max_weight': int(np.abs(integer_weights).max()),
                                  'file': str(filename), 'seconds': result['seconds']}), flush=True)
                return {'node': bank['node'], 'status': 'exact_separation', 'file': str(filename),
                        'margin': total - cost_sum, 'seconds': result['seconds']}
        if not violated or time.monotonic() - start >= seconds:
            break
        for i, ps, ns in violated:
            add(i, ps, ns)
    return {'node': bank['node'], 'status': 'no_separation', 'iterations': it + 1,
            'last_valid_float_gap': last_valid, 'seconds': time.monotonic() - start}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('banks')
    parser.add_argument('output')
    parser.add_argument('--prefix', default='Dynamic')
    parser.add_argument('--seconds', type=float, default=45.)
    parser.add_argument('--iterations', type=int, default=250)
    parser.add_argument('--minimum-gap', type=float, default=0.)
    parser.add_argument('--nodes', type=int, nargs='*')
    args = parser.parse_args()
    source = Path(args.banks).read_text()
    banks = json.loads(source) if source.lstrip().startswith('[') else [json.loads(x) for x in source.splitlines()]
    if args.nodes:
        by_id = {b['node']: b for b in banks}
        banks = [by_id[n] for n in args.nodes]
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=True)
    results = [solve(b, args.seconds, args.iterations, output, args.prefix, args.minimum_gap) for b in banks]
    (output / 'summary.json').write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps({'summary': results}), flush=True)


if __name__ == '__main__':
    main()
