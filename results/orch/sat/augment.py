import argparse
import itertools
import json
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('input')
p.add_argument('output')
p.add_argument('--n', type=int, default=10)
p.add_argument('--s', type=int, default=19)
p.add_argument('--max-not', type=int, default=4)
p.add_argument('--binary-floor', type=int, default=15)
p.add_argument('--not-or-pad', action='store_true')
p.add_argument('--exact-not', type=int)
p.add_argument('--first-not', action='store_true')
p.add_argument('--incomparable-rows')
p.add_argument('--petersen-first', action='store_true')
p.add_argument('--petersen-read-bounds', action='store_true')
args = p.parse_args()
lines = Path(args.input).read_text().splitlines()
header = lines[0].split()
nv, nc = int(header[2]), int(header[3])
n, s = args.n, args.s
A = 2**n + n + s + 2
ix = lambda kind, j, a: (kind * (s + 1) + j) * A + a + 1
cs = []
for comb in itertools.combinations(range(s), args.max_not + 1):
    cs.append([-ix(0, j, 3) for j in comb])
for j in range(s):
    for a, b in itertools.combinations(range(4), 2):
        cs.append([-ix(0, j, a), -ix(0, j, b)])
    for side in (1, 2):
        for a, b in itertools.combinations(range(n + j + 1), 2):
            cs.append([-ix(side, j, a), -ix(side, j, b)])
for a, b in itertools.combinations(range(n + s + 1), 2):
    cs.append([-ix(6, 0, a), -ix(6, 0, b)])
if args.not_or_pad:
    cs.append([ix(0, j, 3) for j in range(s)] + [ix(7, 0, 0)])
if args.exact_not is not None:
    for comb in itertools.combinations(range(s), s - args.exact_not + 1):
        cs.append([ix(0, j, 3) for j in comb])
    for comb in itertools.combinations(range(s), args.exact_not + 1):
        cs.append([-ix(0, j, 3) for j in comb])
if args.first_not:
    cs.extend([[ix(0, 0, 3)], [ix(1, 0, 0)], [ix(2, 0, 0)]])
if args.petersen_first:
    assert n == 10
    for j in range(s):
        escape = [ix(7,j,0)] + ([-ix(7,j-1,0)] if j else [])
        cs.append(escape+[ix(1,j,0)])
        cs.append(escape+[ix(2,j,k) for k in (0,1,2)])
if args.petersen_read_bounds:
    assert n == 10 and s == 19
    budget = s - args.binary_floor
    assert 0 <= budget < s
    for pad_count in range(1,budget+1):
        for comb in itertools.combinations(range(s), budget+1-pad_count):
            cs.append([-ix(7,pad_count-1,0)]+[-ix(0,j,3) for j in comb])
    cs.append([-ix(7,budget,0)])
    for j in range(s):
        first_escape = [ix(7,j,0)] + ([-ix(7,j-1,0)] if j else [])
        for b in (1,2):
            for a in (0,b):
                cs.append(first_escape+[-ix(2,j,b)]+
                          [ix(side,k,a) for k in range(j+1,s) for side in (1,2)])
        or_nonedge_escape = first_escape+[-ix(0,j,1),-ix(2,j,2)]
        if j <= 2:
            for comb in itertools.combinations(range(s),3-j):
                cs.append(or_nonedge_escape+[-ix(0,k,3) for k in comb])
        else:
            cs.append(or_nonedge_escape)
        not_escape = first_escape+[-ix(0,j,3)]
        if j > 3:
            cs.append(not_escape)
            continue
        readers = []
        for k in range(j+1,s):
            nv += 1
            r = nv
            reads = [ix(side,k,a) for side in (1,2) for a in (0,n+j)]
            cs.extend([[-v,r] for v in reads])
            cs.append([-r]+reads)
            readers.append(r)
        for comb in itertools.combinations(readers,4-j):
            cs.append(not_escape+[-r for r in comb])
if args.incomparable_rows:
    rows = json.loads(Path(args.incomparable_rows).read_text())
    for j in range(s):
        left, right = [], []
        for row in rows:
            nv += 1
            u = nv
            nv += 1
            v = nv
            a, b = ix(4, j, row), ix(5, j, row)
            cs.extend([[-u,a],[-u,-b],[-v,-a],[-v,b]])
            left.append(u)
            right.append(v)
        escape = [ix(7,j,0),ix(0,j,3)]
        cs.extend([left+escape,right+escape])
        cs.append([-ix(0,j,3)]+[ix(4,j,row) for row in rows])
        cs.append([-ix(0,j,3)]+[-ix(4,j,row) for row in rows])
Path(args.output).write_text(
    f'p cnf {nv} {nc + len(cs)}\n' + '\n'.join(lines[1:]) + '\n' +
    ''.join(' '.join(map(str, c)) + ' 0\n' for c in cs))
print(f'vars={nv} clauses={nc + len(cs)} added={len(cs)}')
