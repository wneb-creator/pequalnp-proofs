import argparse
import json
import itertools
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--gates', type=int, default=26)
    ap.add_argument('--out', required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--private', action='store_true')
    ap.add_argument('--pencil', action='store_true')
    ap.add_argument('--strict', action='store_true')
    args = ap.parse_args()
    k = args.k
    groups = ([tuple(range(k))] if args.pencil else list(itertools.combinations(range(k),2)))
    if args.private:
        groups.extend((i,) for i in range(k))
    n = k + len(groups)
    edges = [(i, k+j) for j,grp in enumerate(groups) for i in grp]
    positive = [(1 << p) | (1 << l) for p, l in edges]
    negative = []
    groups_bits = [sum(1<<r for r in grp) for grp in groups]
    for points in range(1 << k):
        lines = [j for j,group in enumerate(groups_bits) if not points&group]
        if all(points>>i&1 or any(groups_bits[j]>>i&1 for j in lines) for i in range(k)):
            negative.append(points | sum(1<<(k+j) for j in lines))
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
        if args.strict:
            for op, pats in ((-ops[i],range(len(positive))), (ops[i],range(len(positive),len(patterns)))):
                for side1,side2 in ((lv[i],rv[i]),(rv[i],lv[i])):
                    witnesses=[]
                    for t in pats:
                        wt=var()
                        witnesses.append(wt)
                        add(-wt,side1[t])
                        add(-wt,-side2[t])
                    add(-op,*witnesses)
        if i:
            for a in range(n + i - 1):
                for b in range(a):
                    add(-rhs[i - 1][a], -rhs[i][b])
    for i in range(n):
        add(*(side[j][i] for j in range(args.gates) for side in (lhs,rhs)))
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
