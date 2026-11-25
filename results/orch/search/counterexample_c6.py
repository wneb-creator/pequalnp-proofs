import argparse
import json
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--gates', type=int, default=8)
    ap.add_argument('--out', required=True)
    ap.add_argument('--first', type=int, choices=[1, 2, 3])
    args = ap.parse_args()
    n = 6
    edges = [(i,(i+1)%6) for i in range(6)]
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
    exact = [[var() for k in range(3)] for i in range(args.gates)]
    left_exact = [[var() for k in range(3)] for i in range(args.gates)]
    right_exact = [[var() for k in range(3)] for i in range(args.gates)]
    def and_equiv(v,a,b):
        add(-v,a); add(-v,b); add(v,-a,-b)
    def conditional_or(condition,v,a,b):
        add(-condition,v,-a); add(-condition,v,-b); add(-condition,-v,a,b)
    for i in range(args.gates):
        for selections,bits in ((lhs[i],left_exact[i]),(rhs[i],right_exact[i])):
            for j,sel in enumerate(selections):
                for k,bit in enumerate(bits):
                    if j<n:
                        val = (j==0 and k==0) or (j==1 and k==1)
                        add(-sel,bit if val else -bit)
                    else:
                        w=exact[j-n][k]
                        add(-sel,-bit,w); add(-sel,bit,-w)
        o=ops[i]
        for k in range(2):
            add(-o,-exact[i][k])
            conditional_or(-o,exact[i][k],left_exact[i][k],right_exact[i][k])
        ab,ba=var(),var()
        and_equiv(ab,left_exact[i][0],right_exact[i][1])
        and_equiv(ba,left_exact[i][1],right_exact[i][0])
        conditional_or(o,exact[i][2],ab,ba)
        conditional_or(-o,exact[i][2],left_exact[i][2],right_exact[i][2])
    add(-exact[-1][2])
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
