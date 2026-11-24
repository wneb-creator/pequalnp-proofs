import argparse
import itertools
import json
import random
import time

from rectangle_search import Circuit, bits, c4free, edge, mincover, verify


def realize(n, rectangles, filters, repair):
    circuit = Circuit(n)
    rs = [circuit.gate("and", circuit.any(bits(a)), circuit.any(bits(b)))
          for a, b in rectangles]
    outputs = []
    for ra, rb, left, right in filters:
        la = circuit.any(bits(left))
        lb = circuit.any(bits(right))
        if ra >= 0:
            la = circuit.gate("or", rs[ra], la)
        if rb >= 0:
            lb = circuit.gate("or", rs[rb], lb)
        outputs.append(circuit.gate("and", la, lb))
    if repair:
        cover = mincover(n, repair)
        stars = {}
        for e in repair:
            center = next(bits(e & cover))
            stars[center] = stars.get(center, 0) | (e & ~(1 << center))
        for center, ns in stars.items():
            outputs.append(circuit.gate("and", center, circuit.any(bits(ns))))
    output = circuit.any(outputs)
    circuit, output = circuit.compact(output)
    return len(circuit.gs), circuit, output


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--trials", type=int, default=100000)
    parser.add_argument("--seed", type=int, default=2029)
    parser.add_argument("--output", required=True)
    parser.add_argument("--require-both", action="store_true")
    args = parser.parse_args()
    rng = random.Random(args.seed)
    start = time.time()
    counts = {"trials": 0, "initial_c4free": 0, "repaired": 0}
    best = 100
    for trial in range(args.trials):
        counts["trials"] += 1
        n = rng.randint(8, 14)
        rectangles = []
        rect_terms = []
        for _ in range(2):
            p, q = rng.randint(2, 3), rng.randint(2, 3)
            vertices = rng.sample(range(n), p + q)
            a = sum(1 << i for i in vertices[:p])
            b = sum(1 << i for i in vertices[p:])
            rectangles.append((a, b))
            rect_terms.append({edge(u, v) for u in bits(a) for v in bits(b)})
        k = rng.randint(2, 5) if args.require_both else rng.randint(1, 4)
        filters = []
        terms = set()
        for filter_index in range(k):
            center = rng.randrange(n)
            width = rng.randint(1, 3)
            leaves = rng.sample([i for i in range(n) if i != center], width)
            left, right = 1 << center, sum(1 << i for i in leaves)
            if rng.random() < 0.5:
                left, right = right, left
            ra = filter_index % 2 if args.require_both else rng.randrange(2)
            rb = rng.choice([-1, 0, 1])
            filters.append((ra, rb, left, right))
            la = rect_terms[ra] | {1 << i for i in bits(left)}
            lb = {1 << i for i in bits(right)}
            if rb >= 0:
                lb |= rect_terms[rb]
            terms.update(a | b for a in la for b in lb)
        es = {t for t in terms if t.bit_count() == 2}
        if not c4free(n, es):
            continue
        counts["initial_c4free"] += 1
        higher = [t for t in terms if t.bit_count() > 2
                  and not any(e & t == e for e in es)]
        repair = set()
        while higher:
            candidates = {edge(u, v) for t in higher
                          for u, v in itertools.combinations(bits(t), 2)}
            safe = [e for e in candidates if c4free(n, es | {e})]
            if not safe:
                break
            scores = [(sum(e & t == e for t in higher), rng.random(), e) for e in safe]
            chosen = max(scores)[2]
            es.add(chosen)
            repair.add(chosen)
            higher = [t for t in higher if t & chosen != chosen]
        if higher:
            continue
        counts["repaired"] += 1
        cover = mincover(n, es)
        lower = len(es) + cover.bit_count() - 1
        cost, circuit, output = realize(n, rectangles, filters, repair)
        margin = cost - lower
        if margin < best:
            best = margin
            record = dict(n=n, rectangles=rectangles, filters=filters,
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
    print(json.dumps(dict(final=True, counts=counts, best=best, elapsed=time.time()-start)), flush=True)


if __name__ == "__main__":
    main()
