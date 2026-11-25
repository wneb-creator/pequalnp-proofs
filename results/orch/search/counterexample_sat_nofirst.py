import argparse
import json
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--gates', type=int, default=26)
    ap.add_argument('--out', required=True)
    ap.add_argument('--first', type=int, choices=[1, 7, 8])
    args = ap.parse_args()
    n = 14
    lines = [{l, (l + 1) % 7, (l + 3) % 7} for l in range(7)]
    edges = [(p, 7 + l) for l, points in enumerate(lines) for p in sorted(points)]
    positive = [(1 << p) | (1 << l) for p, l in edges]
    negative = []
    target = lambda a: any((a >> p) & 1 and (a >> l) & 1 for p, l in edges)
    for a in range(1 << n):
        if not target(a) and all(target(a | (1 << v)) for v in range(n) if not (a >> v) & 1):
            negative.append(a)
    patterns = positive + negative
    count = 0
    clauses = []

    def var():
        nonlocal count
        count += 1
        return count

    def add(*lits):
        clauses.append(lits)

    def exactly_one(vs):
        add(*vs)
        for j, v in enumerate(vs):
            for w in vs[:j]:
                add(-v, -w)

    ops, lhs, rhs, values, lv, rv = [], [], [], [], [], []
    for i in range(args.gates):
        ops.append(var())
        lhs.append([var() for j in range(n + i)])
        rhs.append([var() for j in range(n + i)])
        values.append([var() for t in patterns])
        lv.append([var() for t in patterns])
        rv.append([var() for t in patterns])
    for i in range(args.gates):
        exactly_one(lhs[i])
        exactly_one(rhs[i])
        for a in range(n + i):
            for b in range(a + 1):
                add(-lhs[i][a], -rhs[i][b])
        for t, mask in enumerate(patterns):
            for selections, bit in ((lhs[i], lv[i][t]), (rhs[i], rv[i][t])):
                for j, sel in enumerate(selections):
                    if j < n:
                        add(-sel, bit if (mask >> j) & 1 else -bit)
                    else:
                        wire = values[j - n][t]
                        add(-sel, -bit, wire)
                        add(-sel, bit, -wire)
            o, l, r, v = ops[i], lv[i][t], rv[i][t], values[i][t]
            add(-o, -v, l)
            add(-o, -v, r)
            add(-o, v, -l, -r)
            add(o, v, -l)
            add(o, v, -r)
            add(o, -v, l, r)
        if i:
            for a in range(n + i - 1):
                for b in range(a):
                    add(-rhs[i - 1][a], -rhs[i][b])
    for i in range(args.gates - 1):
        add(*(side[j][n + i] for j in range(i + 1, args.gates) for side in (lhs, rhs)))
    for t in range(len(patterns)):
        add(values[-1][t] if t < len(positive) else -values[-1][t])
    out = Path(args.out)
    with out.open('w') as f:
        f.write(f'p cnf {count} {len(clauses)}\n')
        for c in clauses:
            f.write(' '.join(map(str, c)) + ' 0\n')
    out.with_suffix('.json').write_text(json.dumps(dict(n=n, gates=args.gates, edges=edges,
        patterns=patterns, positive=len(positive), ops=ops, lhs=lhs, rhs=rhs, values=values,
        lv=lv, rv=rv)))
    print(json.dumps(dict(variables=count, clauses=len(clauses), positive=len(positive),
                         negative=len(negative), gates=args.gates)))


if __name__ == '__main__':
    main()
