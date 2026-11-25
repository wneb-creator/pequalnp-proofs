import argparse
import itertools
import json
import time

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_array


def partial_tests(n, edges):
    adj = [0] * n
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    negatives = []
    positives = set()
    for mask in range(1 << n):
        if any((mask >> a) & 1 and mask & adj[a] for a in range(n)):
            continue
        if any(not (mask >> a) & 1 and not mask & adj[a] for a in range(n)):
            continue
        negatives.append(mask)
        for a in range(n):
            if not (mask >> a) & 1:
                positives.add(mask | (1 << a))
    return negatives, sorted(positives)


def solve(n, edges, k, limit=60):
    labels = []
    costs = []
    rows, cols, vals, lows, highs = [], [], [], [], []

    def var(label, cost=0):
        labels.append(label)
        costs.append(cost)
        return len(labels) - 1

    def con(pairs, lo=-np.inf, hi=np.inf):
        r = len(lows)
        for c, v in pairs:
            rows.append(r)
            cols.append(c)
            vals.append(v)
        lows.append(lo)
        highs.append(hi)

    def product(a, b, label):
        p = var(label)
        con([(p, 1), (a, -1)], hi=0)
        con([(p, 1), (b, -1)], hi=0)
        con([(p, 1), (a, -1), (b, -1)], lo=-1)
        return p

    selectors = [[[var(('sel', i, side, x), 0.001) for x in range(n + i)] for side in range(2)] for i in range(k)]
    outputs = [var(('out', i), 0.001) for i in range(k)]
    if k:
        con([(outputs[-1], 1)], lo=1, hi=1)
    negatives, positives = partial_tests(n, edges)
    for ti, mask in enumerate(negatives + positives):
        values = []
        for i in range(k):
            sides = []
            for side in range(2):
                selected = [selectors[i][side][x] for x in range(n) if (mask >> x) & 1]
                selected.extend(product(selectors[i][side][n+j], values[j], ('prod', ti, i, side, j)) for j in range(i))
                s = var(('side', ti, i, side))
                for v in selected:
                    con([(s, 1), (v, -1)], lo=0)
                con([(s, 1)] + [(v, -1) for v in selected], hi=0)
                sides.append(s)
            value = product(sides[0], sides[1], ('gate', ti, i))
            values.append(value)
        outterms = [product(outputs[i], values[i], ('outprod', ti, i)) for i in range(k)]
        if ti < len(negatives):
            con([(v, 1) for v in outterms], hi=0)
        else:
            con([(v, 1) for v in outterms], lo=1)
    matrix = coo_array((np.asarray(vals, dtype=float), (np.asarray(rows, dtype=np.int32), np.asarray(cols, dtype=np.int32))), shape=(len(lows), len(labels))).tocsc()
    started = time.monotonic()
    result = milp(np.asarray(costs), integrality=np.ones(len(labels), dtype=np.int32), bounds=Bounds(0, 1), constraints=LinearConstraint(matrix, lows, highs), options={'time_limit': limit})
    answer = {'status': int(result.status), 'message': result.message, 'seconds': time.monotonic()-started, 'k': k, 'negative': negatives, 'positive': positives}
    if result.x is not None:
        answer['gates'] = [[[j for j, idx in enumerate(side) if result.x[idx] > 0.5] for side in gate] for gate in selectors]
        answer['outputs'] = [i for i, idx in enumerate(outputs) if result.x[idx] > 0.5]
        def evaluate(mask):
            truth = [bool(mask & (1 << i)) for i in range(n)]
            for left, right in answer['gates']:
                truth.append(any(truth[x] for x in left) and any(truth[x] for x in right))
            return any(truth[n+i] for i in answer['outputs'])
        answer['verified'] = all(not evaluate(s) for s in negatives) and all(evaluate(s) for s in positives)
        assert answer['verified']
    return answer


def examples():
    all_edges = set(itertools.combinations(range(6), 2))
    cycle = {(min(i,(i+1)%6), max(i,(i+1)%6)) for i in range(6)}
    prism = {(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)}
    wheel = {(min(i,(i+1)%5), max(i,(i+1)%5)) for i in range(5)} | {(i,5) for i in range(5)}
    return {'cycle6':cycle, 'prism':prism, 'wheel5':wheel, 'complete6':all_edges, 'complement_cycle6':all_edges-cycle, 'complement_prism':all_edges-prism, 'path6':{(i,i+1) for i in range(5)}, 'two_triangles':{(0,1),(1,2),(0,2),(3,4),(4,5),(3,5)}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--limit', type=float, default=60)
    parser.add_argument('--gates', type=int, default=2)
    args = parser.parse_args()
    for name, edges in examples().items():
        answer = solve(6, sorted(edges), args.gates, args.limit)
        answer.update(name=name, edges=sorted(edges))
        print(json.dumps(answer), flush=True)
