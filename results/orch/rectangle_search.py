import argparse
import functools
import itertools
import json
import random
import time


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


def edge(u, v):
    return (1 << u) | (1 << v)


def c4free(n, es):
    hood = [0] * n
    for e in es:
        u, v = bits(e)
        hood[u] |= 1 << v
        hood[v] |= 1 << u
    return all((hood[u] & hood[v]).bit_count() <= 1
               for u, v in itertools.combinations(range(n), 2))


def mincover(n, es):
    es = tuple(es)

    @functools.lru_cache(None)
    def solve(rem):
        surviving = next((e for e in es if e & rem == e), None)
        if surviving is None:
            return 0
        u, v = bits(surviving)
        cu = (1 << u) | solve(rem & ~(1 << u))
        cv = (1 << v) | solve(rem & ~(1 << v))
        return min((cu, cv), key=int.bit_count)

    return solve((1 << n) - 1)


class Circuit:
    def __init__(self, n):
        self.n = n
        self.gs = []
        self.intern = {}

    def gate(self, op, a, b):
        if a == b:
            return a
        a, b = sorted((a, b))
        key = (op, a, b)
        if key not in self.intern:
            self.intern[key] = self.n + len(self.gs)
            self.gs.append(key)
        return self.intern[key]

    def any(self, vs):
        vs = sorted(set(vs))
        a = vs[0]
        for b in vs[1:]:
            a = self.gate("or", a, b)
        return a

    def live(self, output):
        seen = set()

        def walk(w):
            if w < self.n or w in seen:
                return
            seen.add(w)
            _, a, b = self.gs[w - self.n]
            walk(a)
            walk(b)

        walk(output)
        return len(seen)

    def compact(self, output):
        live = set()

        def visit(w):
            if w < self.n or w in live:
                return
            live.add(w)
            _, a, b = self.gs[w - self.n]
            visit(a)
            visit(b)

        visit(output)
        result = Circuit(self.n)
        mapping = {i: i for i in range(self.n)}
        for j, (op, a, b) in enumerate(self.gs):
            old = self.n + j
            if old in live:
                mapping[old] = result.gate(op, mapping[a], mapping[b])
        return result, mapping[output]


def realize(n, a, b, filters, repair):
    circuit = Circuit(n)
    r = circuit.gate("and", circuit.any(bits(a)), circuit.any(bits(b)))
    outputs = []
    for left, right in filters:
        f = circuit.gate("or", r, circuit.any(bits(left)))
        outputs.append(circuit.gate("and", f, circuit.any(bits(right))))
    if repair:
        cover = mincover(n, repair)
        stars = {}
        for e in repair:
            candidates = list(bits(e & cover))
            center = candidates[0]
            stars[center] = stars.get(center, 0) | (e & ~(1 << center))
        for center, ns in stars.items():
            outputs.append(circuit.gate("and", center, circuit.any(bits(ns))))
    output = circuit.any(outputs)
    circuit, output = circuit.compact(output)
    return len(circuit.gs), circuit, output


def verify(n, es, circuit, output):
    for x in range(1 << n):
        wires = [bool(x & (1 << i)) for i in range(n)]
        for op, a, b in circuit.gs:
            wires.append((wires[a] and wires[b]) if op == "and" else
                         (wires[a] or wires[b]))
        if wires[output] != any(x & e == e for e in es):
            return False
    return True


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--trials", type=int, default=100000)
    parser.add_argument("--seed", type=int, default=2028)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    start = time.time()
    counts = {"trials": 0, "initial_c4free": 0, "repaired": 0}
    best = 100
    for trial in range(args.trials):
        counts["trials"] += 1
        n = rng.randint(8, 14)
        p, q = rng.randint(2, 4), rng.randint(2, 4)
        vertices = rng.sample(range(n), p + q)
        a = sum(1 << i for i in vertices[:p])
        b = sum(1 << i for i in vertices[p:])
        rect = {edge(u, v) for u in bits(a) for v in bits(b)}
        k = rng.randint(2, 5)
        filters = []
        terms = set()
        for _ in range(k):
            center = rng.randrange(n)
            width = rng.randint(1, 4)
            leaves = rng.sample([i for i in range(n) if i != center], width)
            left, right = 1 << center, sum(1 << i for i in leaves)
            if rng.random() < 0.3:
                left, right = right, left
            filters.append((left, right))
            terms.update(edge(u, v) for u in bits(left) for v in bits(right))
            terms.update(e | (1 << v) for e in rect for v in bits(right))
        es = {t for t in terms if t.bit_count() == 2}
        if not c4free(n, es):
            continue
        counts["initial_c4free"] += 1
        triples = [t for t in terms if t.bit_count() == 3
                   and not any(e & t == e for e in es)]
        repair = set()
        while triples:
            candidates = {edge(u, v) for t in triples
                          for u, v in itertools.combinations(bits(t), 2)}
            safe = [e for e in candidates if c4free(n, es | {e})]
            if not safe:
                break
            scores = [(sum(e & t == e for t in triples), rng.random(), e) for e in safe]
            chosen = max(scores)[2]
            es.add(chosen)
            repair.add(chosen)
            triples = [t for t in triples if t & chosen != chosen]
        if triples:
            continue
        counts["repaired"] += 1
        cover = mincover(n, es)
        lower = len(es) + cover.bit_count() - 1
        cost, circuit, output = realize(n, a, b, filters, repair)
        margin = cost - lower
        if margin < best:
            best = margin
            record = dict(n=n, a=a, b=b, filters=filters,
                          edges=sorted(es), repair=sorted(repair),
                          cover=cover, size=cost, bound=lower, margin=margin,
                          gates=circuit.gs, output=output, counts=counts.copy(),
                          verified=verify(n, es, circuit, output),
                          elapsed=time.time()-start)
            if not record["verified"]:
                raise RuntimeError("independent truth-table verification failed")
            with open(args.output, "w") as f:
                json.dump(record, f, indent=2)
            print(json.dumps({k:record[k] for k in ["n", "size", "bound", "margin", "verified", "elapsed", "counts"]}), flush=True)
            if margin < 0 and record["verified"]:
                break
        if trial and trial % 10000 == 0:
            print(json.dumps(dict(counts=counts, best=best, elapsed=time.time()-start)), flush=True)
    print(json.dumps(dict(final=True, counts=counts, best=best, elapsed=time.time()-start)), flush=True)


if __name__ == "__main__":
    main()
