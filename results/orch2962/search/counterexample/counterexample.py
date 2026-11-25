"""Exact finite dead-core evaluator and bounded randomized circuit search.

All gates are backward binary AND/OR. The eventual live output is an independent
star-cover circuit, so all searched gates can be dead and lift fixedness is automatic.
No result from this program is a formal Lean certificate.
"""

import argparse
import json
import math
from pathlib import Path
import random
import time


class Graph:
    def __init__(self, n, edges):
        self.n, self.edges = n, [tuple(sorted(e)) for e in edges]
        self.m = len(edges)
        self.tt = [sum(1 << x for x in range(1 << n) if x >> v & 1) for v in range(n)]
        self.acc = [sum(1 << i for i, e in enumerate(self.edges) if v in e) for v in range(n)]
        self.target = 0
        for u, v in edges:
            self.target |= self.tt[u] & self.tt[v]
        self.neighbors = [sum(1 << v for u, v in self.edges if u == a) |
                          sum(1 << u for u, v in self.edges if v == a) for a in range(n)]
        self.cover_cache = {0: 0}
        self.tau = self.cover((1 << self.m) - 1)

    def cover(self, edges):
        if edges in self.cover_cache:
            return self.cover_cache[edges]
        first = (edges & -edges).bit_length()-1
        u, v = self.edges[first]
        best = 1 + min(self.cover(edges & ~self.acc[u]), self.cover(edges & ~self.acc[v]))
        self.cover_cache[edges] = best
        return best

    def cross(self, a, b):
        return sum(1 << i for i, (u, v) in enumerate(self.edges)
                   if (a >> u & 1 and b >> v & 1) or (a >> v & 1 and b >> u & 1))

    def evaluate(self, gates, detail=False):
        tt, acc = self.tt.copy(), self.acc.copy()
        single = [1 << v for v in range(self.n)]
        pair, cone, imp = [0] * self.n, [0] * self.n, [False] * self.n
        cores = 0
        core_ancestors = 0
        for g, (op, a, b) in enumerate(gates):
            value = tt[a] | tt[b] if op else tt[a] & tt[b]
            accepted = acc[a] | acc[b] if op else acc[a] & acc[b]
            singleton = single[a] | single[b] if op else 0
            pairs = pair[a] | pair[b] if op else self.cross(single[a], single[b])
            below = bool(value) and not value & ~self.target
            ancestors = cone[a] | cone[b]
            if below and not (imp[a] and imp[b]) and accepted & ~pairs:
                cores |= 1 << g
                core_ancestors |= ancestors
            tt.append(value); acc.append(accepted); single.append(singleton)
            pair.append(pairs); cone.append(ancestors | (1 << g)); imp.append(below)
        maximal = cores & ~core_ancestors
        union, incidences, cone_sum = 0, 0, 0
        for g in range(len(gates)):
            if maximal >> g & 1:
                union |= cone[self.n + g]
                incidences |= acc[self.n + g]
                cone_sum += cone[self.n + g].bit_count()
        remainder = ((1 << self.m) - 1) & ~incidences
        left = incidences.bit_count() + self.tau
        right = union.bit_count() + maximal.bit_count() + self.cover(remainder)
        tau_d = self.cover(incidences)
        strong_margin = union.bit_count() + maximal.bit_count() - incidences.bit_count() - tau_d
        input_ports = sum((a < self.n) + (b < self.n) for g, (_, a, b) in enumerate(gates) if union >> g & 1)
        leaf_margin = input_ports - incidences.bit_count() - tau_d
        posted_leaf_margin = input_ports - incidences.bit_count() - self.tau + self.cover(remainder)
        ors = sum(op for g, (op, _, _) in enumerate(gates) if union >> g & 1)
        ands = union.bit_count() - ors
        or_margin = ors + maximal.bit_count() - incidences.bit_count()
        and_margin = ands + self.cover(remainder) - self.tau
        overlap = cone_sum - union.bit_count()
        if detail:
            return dict(n=self.n, edges=self.edges, gates=gates, cores=cores,
                        maximal=maximal, union=union, incidences=incidences,
                        tau=self.tau, tau_remainder=self.cover(remainder),
                        tau_D=tau_d, strong_margin=strong_margin,
                        input_ports=input_ports, leaf_margin=leaf_margin, posted_leaf_margin=posted_leaf_margin,
                        ors=ors, ands=ands, or_margin=or_margin, and_margin=and_margin, overlap=overlap,
                        left=left, right=right, margin=right-left)
        return (right-left, incidences.bit_count(), maximal.bit_count(), strong_margin, leaf_margin, posted_leaf_margin, or_margin, and_margin, overlap)


def seed_circuit(graph, count, rng):
    gs = [(0, u, v) for u, v in graph.edges]
    while len(gs) < count:
        j = len(gs)
        if rng.random() < .6 and j > graph.m:
            a = rng.randrange(graph.n + j)
            b = rng.randrange(graph.n)
            op = rng.randrange(2)
        else:
            a, b, op = rng.randrange(graph.n + j), rng.randrange(graph.n + j), rng.randrange(2)
        gs.append((op, min(a, b), max(a, b)))
    return gs[:count]


def search(graph, seconds, seed, output, objective='posted', min_cores=0):
    rng = random.Random(seed)
    started = time.monotonic()
    best = (1000, 0, 0)
    best_strong = 1000
    best_leaf = 1000
    best_split = [1000,1000]
    champion, champion_score = None, 1000
    def score(result):
        if not result[1]:
            return 100
        if result[2] < min_cores:
            return 50-result[2]
        if objective == 'or':
            return result[6] / math.sqrt(result[1]) - .02*result[1]
        if objective == 'and':
            return result[7] / math.sqrt(result[1]) - .02*result[1]
        if objective == 'strong':
            return result[3] / math.sqrt(result[1]) - .02*result[1]
        if objective == 'large':
            return result[0] / math.sqrt(result[1]) - .02*result[1]
        return result[0] - .03*result[1]
    trials = 0
    while time.monotonic() - started < seconds:
        if champion is not None and rng.random() < .7:
            gs = champion.copy()
            count = len(gs)
        else:
            count = rng.randrange(max(4, graph.m), max(5, 3 * graph.m + 5))
            gs = seed_circuit(graph, count, rng)
        old = graph.evaluate(gs)
        for step in range(1000):
            if time.monotonic() - started >= seconds:
                break
            trials += 1
            j = rng.randrange(count)
            prior = gs[j]
            op, a, b = prior
            change = rng.randrange(3)
            if change == 0: op = 1-op
            elif change == 1: a = rng.randrange(graph.n+j)
            else: b = rng.randrange(graph.n+j)
            gs[j] = (op, min(a,b), max(a,b))
            new = graph.evaluate(gs)
            for k, name in enumerate(('or', 'and')):
                if new[1] and new[6+k] < best_split[k]:
                    best_split[k] = new[6+k]
                    Path(output+'.'+name+'.json').write_text(json.dumps(graph.evaluate(gs, True), indent=2)+'\n')
                    print(json.dumps(dict(split=name,margin=best_split[k],posted_margin=new[0],trials=trials)),flush=True)
            if new[1] and new[4] < best_leaf:
                best_leaf = new[4]
                data = graph.evaluate(gs, True)
                Path(output+'.leaf.json').write_text(json.dumps(data, indent=2)+'\n')
                print(json.dumps(dict(leaf_margin=best_leaf,posted_leaf_margin=new[5],posted_margin=new[0],trials=trials)), flush=True)
            if new[1] and new[3] < best_strong:
                best_strong = new[3]
                data = graph.evaluate(gs, True)
                Path(output+'.strong.json').write_text(json.dumps(data, indent=2)+'\n')
                print(json.dumps(dict(strong_margin=best_strong,posted_margin=new[0],trials=trials)), flush=True)
            if new[1] and (new[0], -new[1], new[2]) < (best[0], -best[1], best[2]):
                best = new
                data = graph.evaluate(gs, True)
                data.update(trials=trials, elapsed=time.monotonic()-started)
                Path(output).write_text(json.dumps(data, indent=2)+'\n')
                print(json.dumps(dict(best=best,trials=trials,elapsed=data['elapsed'])), flush=True)
                if new[0] < 0:
                    print('COUNTEREXAMPLE candidate; requires independent and Lean checking', flush=True)
                    return
            old_score, new_score = score(old), score(new)
            if new_score < champion_score:
                champion_score, champion = new_score, gs.copy()
                Path(output+'.champion.json').write_text(json.dumps(graph.evaluate(gs, True), indent=2)+'\n')
            temperature = .15 + .7*(1-step/1000)
            if new_score <= old_score or rng.random() < math.exp(min(0,(old_score-new_score)/temperature)):
                old = new
            else:
                gs[j] = prior
    print(json.dumps(dict(status='inconclusive', trials=trials, best=best,
                          elapsed=time.monotonic()-started)), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('graph')
    parser.add_argument('seconds', type=float)
    parser.add_argument('seed', type=int)
    parser.add_argument('output')
    parser.add_argument('--objective', choices=['posted', 'strong', 'large', 'or', 'and'], default='posted')
    parser.add_argument('--min-cores', type=int, default=0)
    args = parser.parse_args()
    data = json.loads(Path(args.graph).read_text())
    search(Graph(data['n'], data['edges']), args.seconds, args.seed, args.output, args.objective, args.min_cores)
