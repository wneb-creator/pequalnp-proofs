import argparse
import json
import math
import random
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seconds', type=int, default=300)
    ap.add_argument('--seed', type=int, default=76)
    args = ap.parse_args()
    random.seed(args.seed)
    n = 26
    N = 13
    lines = [{l, (l+1)%N, (l+3)%N, (l+9)%N} for l in range(N)]
    edges = [(p,N+l) for l,L in enumerate(lines) for p in sorted(L)]
    patterns = [(1<<p)|(1<<l) for p,l in edges]
    for a in range(1<<N):
        b=sum(1<<l for l,L in enumerate(lines) if not any((a>>p)&1 for p in L))
        aa=sum(1<<p for p in range(N) if not any((b>>l)&1 and p in L for l,L in enumerate(lines)))
        if aa==a: patterns.append(a|(b<<N))
    masks=[sum(1<<t for t,a in enumerate(patterns) if (a>>i)&1) for i in range(n)]
    target=(1<<len(edges))-1
    nodes = []
    stars = []
    for l,points in enumerate(lines):
        a,b,c,d=sorted(points)
        j=len(nodes)
        nodes.extend([(0,a,b),(0,26+j,c),(0,27+j,d),(1,28+j,13+l)])
        stars.append(29+j)
    o=stars[0]
    for star in stars[1:]:
        nodes.append((0,o,star))
        o=26+len(nodes)-1
    assert len(nodes)==64

    def evaluate(circuit):
        ws = masks.copy()
        for op, a, b in circuit:
            ws.append((ws[a] & ws[b]) if op else (ws[a] | ws[b]))
        bad = ws[-1] ^ target
        return bad.bit_count()

    def restart():
        while True:
            remove = random.randrange(64)
            choose = random.choice(nodes[remove][1:])
            replace = lambda w: choose if w == 26 + remove else w
            shift = lambda w: replace(w) - (replace(w) > 26 + remove)
            c = [(op, shift(a), shift(b)) for j, (op, a, b) in enumerate(nodes) if j != remove]
            if remove < 63:
                return c

    best = len(patterns)
    start = last = time.monotonic()
    c = restart()
    score = evaluate(c)
    iterations = restarts = 0
    while time.monotonic() - start < args.seconds:
        iterations += 1
        if iterations % 15000 == 0:
            c = restart()
            score = evaluate(c)
            restarts += 1
        gate = random.randrange(63)
        old = c[gate]
        op, a, b = old
        choice = random.randrange(8)
        if choice == 0:
            op ^= 1
        elif choice <= 3:
            a = random.randrange(n + gate)
        elif choice <= 6:
            b = random.randrange(n + gate)
        else:
            a, b = random.sample(range(n + gate), 2)
            op = random.randrange(2)
        c[gate] = (op, a, b)
        new = evaluate(c)
        temperature = 0.3 + 3 * (1 - (iterations % 15000) / 15000)
        if new <= score or random.random() < math.exp(min(0, (score - new) / temperature)):
            score = new
        else:
            c[gate] = old
        if score < best:
            best = score
            print(json.dumps(dict(event='best', seconds=time.monotonic() - start,
                                  iterations=iterations, mismatches=best, circuit=c)), flush=True)
            if best == 0:
                return
        if time.monotonic() - last >= 30:
            last = time.monotonic()
            print(json.dumps(dict(event='progress', seconds=last - start,
                                  iterations=iterations, restarts=restarts, best=best)), flush=True)
    print(json.dumps(dict(event='finished', seconds=time.monotonic() - start,
                          iterations=iterations, restarts=restarts, best=best)), flush=True)


if __name__ == '__main__':
    main()
