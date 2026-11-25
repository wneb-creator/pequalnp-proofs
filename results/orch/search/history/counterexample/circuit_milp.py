import argparse
import itertools
import json
import time
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


def solve(n, edges, gates, seconds, first_pairs=None, honest=False):
    edges = {tuple(sorted(e)) for e in edges}
    def target(a):
        return any((a >> i) & (a >> j) & 1 for i, j in edges)
    positives = sorted({(1 << i) | (1 << j) for i, j in edges})
    negatives = [a for a in range(1 << n) if not target(a) and
                 all(target(a | (1 << i)) for i in range(n) if not a & (1 << i))]
    assignments = positives + negatives
    truth = [1] * len(positives) + [0] * len(negatives)
    choices = []
    columns = []
    nextvar = 0
    for g in range(gates):
        cs = []
        pairs = first_pairs if g == 0 and first_pairs else itertools.combinations(range(n + g), 2)
        for i, j in pairs:
            for op in (0, 1):
                cs.append((nextvar, op, i, j))
                nextvar += 1
        choices.append(cs)
    selector_count = nextvar
    val = {}
    for g in range(gates):
        for a in assignments:
            val[g, a] = nextvar
            nextvar += 1
    rowidx, colidx, data, lo, hi = [], [], [], [], []
    def constraint(terms, lower=-np.inf, upper=np.inf):
        row = len(lo)
        for c, x in terms:
            rowidx.append(row); colidx.append(x); data.append(c)
        lo.append(lower); hi.append(upper)
    def wire(i, a, coef):
        if i < n:
            return [], coef * ((a >> i) & 1)
        return [(coef, val[i - n, a])], 0
    def inequality(s, g, a, vi, vj, out, upper):
        terms = [(1, s), (out, val[g, a])]
        offset = 0
        for i, coef in ((vi[0], vi[1]), (vj[0], vj[1])):
            ts, c = wire(i, a, coef)
            terms.extend(ts); offset += c
        constraint(terms, upper=upper - offset)
    for g, cs in enumerate(choices):
        constraint([(1, s) for s, _, _, _ in cs], 1, 1)
        for s, op, i, j in cs:
            for a in assignments:
                if op == 0:
                    # s=1 implies out <= x, out <= y, out >= x+y-1.
                    inequality(s, g, a, (i, -1), (j, 0), 1, 1)
                    inequality(s, g, a, (i, 0), (j, -1), 1, 1)
                    inequality(s, g, a, (i, 1), (j, 1), -1, 2)
                    if honest and not target(a):
                        constraint([(1, s), (1, val[g, a])], upper=1)
                else:
                    # s=1 implies out >= x, out >= y, out <= x+y.
                    inequality(s, g, a, (i, 1), (j, 0), -1, 1)
                    inequality(s, g, a, (i, 0), (j, 1), -1, 1)
                    inequality(s, g, a, (i, -1), (j, -1), 1, 1)
    for g in range(gates - 1):
        uses = [(1, s) for cs in choices[g+1:] for s, op, i, j in cs if n + g in (i, j)]
        constraint(uses, lower=1)
    for a, b in zip(assignments, truth):
        constraint([(1, val[gates - 1, a])], b, b)
    mat = coo_matrix((data, (rowidx, colidx)), shape=(len(lo), nextvar)).tocsc()
    print(json.dumps({'n': n, 'edges': sorted(edges), 'gates': gates,
                      'assignments': len(assignments), 'variables': nextvar,
                      'selectors': selector_count, 'constraints': len(lo),
                      'honest': honest}), flush=True)
    start = time.monotonic()
    ans = milp(np.zeros(nextvar), integrality=np.r_[np.ones(selector_count), np.zeros(nextvar-selector_count)],
               bounds=Bounds(np.zeros(nextvar), np.ones(nextvar)),
               constraints=LinearConstraint(mat, np.array(lo), np.array(hi)),
               options={'time_limit': seconds, 'disp': True})
    result = {'status': int(ans.status), 'message': ans.message, 'seconds': time.monotonic()-start}
    if ans.x is not None:
        circuit = []
        for cs in choices:
            picked = [(op, i, j) for s, op, i, j in cs if ans.x[s] > .5]
            assert len(picked) == 1
            circuit.append(picked[0])
        for a in range(1 << n):
            w = [(a >> i) & 1 for i in range(n)]
            for op, i, j in circuit:
                w.append((w[i] | w[j]) if op else (w[i] & w[j]))
            assert bool(w[-1]) == target(a), (a, w, target(a))
        result['circuit'] = circuit
    print(json.dumps(result), flush=True)
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--cycle', type=int, default=5)
    p.add_argument('--gates', type=int, default=6)
    p.add_argument('--seconds', type=float, default=120)
    p.add_argument('--honest', action='store_true')
    p.add_argument('--graph', choices=['cycle', 'theta233', 'petersen'], default='cycle')
    args = p.parse_args()
    n = args.cycle
    edges = [(i, (i+1)%n) for i in range(n)]
    pairs = [(0, j) for j in range(1, n//2+1)]
    if args.graph == 'theta233':
        n = 7
        edges = [(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]
        eset = {tuple(sorted(e)) for e in edges}
        autos = [p for p in itertools.permutations(range(n)) if
                 {tuple(sorted((p[i],p[j]))) for i,j in edges} == eset]
        pairs = []
        seen = set()
        for i,j in itertools.combinations(range(n),2):
            if (i,j) in seen: continue
            pairs.append((i,j))
            seen.update(tuple(sorted((p[i],p[j]))) for p in autos)
        print('first-pair orbit representatives',pairs,flush=True)
    elif args.graph == 'petersen':
        vertices = list(itertools.combinations(range(5),2))
        n = len(vertices)
        edges = [(i,j) for i,j in itertools.combinations(range(n),2)
                 if not (set(vertices[i]) & set(vertices[j]))]
        pairs = [(0,1),(0,7)]
    solve(n, edges, args.gates, args.seconds,
          first_pairs=pairs, honest=args.honest)
