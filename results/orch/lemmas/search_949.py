"""Finite model investigation of L-meta-949. No Lean acceptance claims."""
import argparse
import itertools
import json
import subprocess
import time
from functools import lru_cache
from pathlib import Path

SOLVER = '/tmp/oec/pequalnp-pilot-82/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
SCRATCH = Path('/tmp/oec/pequalnp-pilot-82/finite-search')


def pairs(n):
    return list(itertools.combinations(range(n), 2))


def adjacent(g, n, u, v):
    return u != v and bool(g & (1 << pairs(n).index(tuple(sorted((u, v))))))


@lru_cache(None)
def canonical(g, n):
    es = pairs(n)
    edges = {e for i, e in enumerate(es) if g >> i & 1}
    degree = [sum(v in e for e in edges) for v in range(n)]
    blocks = [[v for v in range(n) if degree[v] == d] for d in sorted(set(degree))]
    best = None
    for choices in itertools.product(*(itertools.permutations(b) for b in blocks)):
        p = sum((tuple(b) for b in choices), ())
        h = sum(1 << i for i, (u, v) in enumerate(es)
                if tuple(sorted((p[u], p[v]))) in edges)
        if best is None or h < best:
            best = h
    return best


def graphs(n):
    reps = {0}
    for m in range(1, n + 1):
        old_pairs = pairs(m - 1)
        new_pairs = pairs(m)
        next_reps = set()
        for g in reps:
            base = sum(1 << new_pairs.index(e) for i, e in enumerate(old_pairs) if g >> i & 1)
            for neighbors in range(1 << (m - 1)):
                h = base | sum(1 << new_pairs.index((v, m - 1))
                               for v in range(m - 1) if neighbors >> v & 1)
                next_reps.add(canonical(h, m))
        reps = next_reps
        print('unlabeled', m, len(reps), flush=True)
    return sorted(reps)


def bicliques(g, n):
    es = pairs(n)
    answer = set()
    for labels in itertools.product(range(3), repeat=n):
        left = [v for v in range(n) if labels[v] == 1]
        right = [v for v in range(n) if labels[v] == 2]
        if not left or not right:
            continue
        cross = {(min(u, v), max(u, v)) for u in left for v in right}
        mask = sum(1 << es.index(e) for e in cross)
        if mask & g == mask:
            answer.add(mask)
    return sorted(x for x in answer if not any(x != y and x & y == x for y in answer))


def cover_number(g, n):
    if not g:
        return 0, []
    bs = bicliques(g, n)
    for k in range(1, n + 1):
        for cover in itertools.combinations(bs, k):
            mask = 0
            for b in cover:
                mask |= b
            if mask == g:
                return k, list(cover)
    raise AssertionError('stars always cover a graph')


def partial_examples(g, n):
    es = [e for i, e in enumerate(pairs(n)) if g >> i & 1]
    independent = [u for u in range(1 << n)
                   if not any(u >> a & 1 and u >> b & 1 for a, b in es)]
    maximal = [u for u in independent
               if all(u >> v & 1 or (u | (1 << v)) not in independent for v in range(n))]
    positive = sorted({u | (1 << v) for u in maximal for v in range(n) if not (u >> v & 1)})
    assert not set(maximal) & set(positive)
    return maximal, positive


class CNF:
    def __init__(self):
        self.n = 0
        self.clauses = []

    def variable(self):
        self.n += 1
        return self.n

    def clause(self, *lits):
        self.clauses.append(list(lits))

    def conjunction(self, a, b):
        q = self.variable()
        self.clause(-q, a)
        self.clause(-q, b)
        self.clause(q, -a, -b)
        return q

    def disjunction(self, values):
        q = self.variable()
        for a in values:
            self.clause(-a, q)
        self.clause(-q, *values)
        return q

    def write(self, path):
        with path.open('w') as f:
            f.write(f'p cnf {self.n} {len(self.clauses)}\n')
            for clause in self.clauses:
                f.write(' '.join(map(str, clause)) + ' 0\n')


def synthesis(g, n, k, seconds, examples=None, symmetry=False, last_output=False, tag=''):
    cnf = CNF()
    # Each side selects a subset of the bare inputs and earlier AND gates.
    selectors = [[[cnf.variable() for _ in range(n + i)] for _ in range(2)] for i in range(k)]
    outputs = [cnf.variable() for _ in range(k)]
    if symmetry:
        for left, right in selectors:
            prefix = cnf.variable()
            cnf.clause(prefix)
            for a, b in zip(left, right):
                cnf.clause(-prefix, -a, b)
                following = cnf.variable()
                cnf.clause(-following, prefix)
                cnf.clause(-following, -a, b)
                cnf.clause(-following, a, -b)
                cnf.clause(-prefix, -a, -b, following)
                cnf.clause(-prefix, a, b, following)
                prefix = following
    if last_output and k:
        cnf.clause(outputs[-1])
    negative, positive = partial_examples(g, n) if examples is None else examples
    for u in negative + positive:
        vals = []
        for i in range(k):
            sides = []
            for s in range(2):
                summands = [selectors[i][s][v] for v in range(n) if u >> v & 1]
                summands += [cnf.conjunction(selectors[i][s][n + j], vals[j]) for j in range(i)]
                sides.append(cnf.disjunction(summands))
            vals.append(cnf.conjunction(*sides))
        if u in negative:
            for i in range(k):
                cnf.clause(-outputs[i], -vals[i])
        else:
            terms = [cnf.conjunction(outputs[i], vals[i]) for i in range(k)]
            cnf.clause(*terms)
    # At least one output when the graph has an edge. No output variables can occur:
    # every vertex belongs to a maximal independent set, which must evaluate false.
    if g:
        cnf.clause(*outputs)
    name = f'n{n}-g{g}-k{k}{tag}'
    path = SCRATCH / (name + '.cnf')
    cnf.write(path)
    with (SCRATCH / (name + '.log')).open('w') as log:
        result = subprocess.run([SOLVER, '-q', '-t', str(seconds), str(path)], stdout=log, stderr=subprocess.STDOUT)
    text = (SCRATCH / (name + '.log')).read_text()
    witness = None
    if result.returncode == 10:
        assignment = {int(v) for line in text.splitlines() if line.startswith('v ') for v in line[2:].split() if int(v) > 0}
        witness = {'sides': [[[j for j, bit in enumerate(side) if bit in assignment] for side in gate] for gate in selectors],
                   'outputs': [i for i, bit in enumerate(outputs) if bit in assignment]}
        for u in negative + positive:
            val = [bool(u >> v & 1) for v in range(n)]
            for left, right in witness['sides']:
                val.append(any(val[j] for j in left) and any(val[j] for j in right))
            out = any(val[n + j] for j in witness['outputs'])
            assert out == (u in positive), (g, u, witness)
    return result.returncode, witness


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--n', type=int, default=6)
    parser.add_argument('--seconds', type=int, default=30)
    parser.add_argument('--start', type=int, default=0)
    args = parser.parse_args()
    SCRATCH.mkdir(exist_ok=True)
    reps = graphs(args.n)
    records = []
    for g in reps:
        bc, cover = cover_number(g, args.n)
        records.append({'graph': g, 'edges': [e for i, e in enumerate(pairs(args.n)) if g >> i & 1],
                        'biclique_cover': bc, 'cover': cover})
    records.sort(key=lambda x: (-x['biclique_cover'], -len(x['edges']), x['graph']))
    (SCRATCH / f'graphs{args.n}.json').write_text(json.dumps(records, indent=2))
    print('cover histogram', {k: sum(r['biclique_cover'] == k for r in records) for k in range(args.n + 1)}, flush=True)
    for index, r in enumerate(records):
        if index < args.start or not r['graph']:
            continue
        stamp = time.time()
        status, witness = synthesis(r['graph'], args.n, r['biclique_cover'] - 1, args.seconds)
        r.update(status=status, witness=witness, seconds=round(time.time() - stamp, 3))
        print(index, json.dumps(r), flush=True)
        (SCRATCH / f'results{args.n}.json').write_text(json.dumps(records, indent=2))
        if witness:
            print('WITNESS FOUND', flush=True)
            break


if __name__ == '__main__':
    main()
