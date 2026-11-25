#!/usr/bin/env python3
"""Literal translation of repository LRAT.LinkN.enc and LRAT.LinkN.enc2.

Clauses preserve Lean order. DIMACS variable d is Lean checker variable d,
so positive DIMACS d is Lean literal 2*d and negative d is 2*d+1.
No extra SAT-only restrictions are introduced.
"""
import argparse
import hashlib
import json
from pathlib import Path


def clauses(n, s, edges, rows):
    width = 2**n + n + s + 2
    def ix(kind, gate, arg):
        return (kind * (s + 1) + gate) * width + arg + 1
    def lit(kind, gate, arg, value):
        var = ix(kind, gate, arg)
        return var if value else -var
    def value(row):
        return any((row >> a & 1) and (row >> b & 1) for a, b in edges)
    # fOp
    for j in range(s):
        yield [ix(0, j, t) for t in range(4)]
    # fSrcAlo
    for e in [1, 2]:
        for j in range(s):
            yield [ix(e, j, k) for k in range(n+j+1)]
    # fSrcEq, in exact e/j/r/k order
    for e in [1, 2]:
        for j in range(s):
            for r in rows:
                for k in range(n+j+1):
                    select = ix(e, j, k)
                    source = ix(e+3, j, r)
                    if k < n:
                        yield [-select, source if (r >> k & 1) else -source]
                    elif k < n+j:
                        wire = ix(3, k-n, r)
                        yield [-select, -source, wire]
                        yield [-select, source, -wire]
                    else:
                        yield [-select, -source]
    # fGate
    for j in range(s):
        for r in rows:
            o = [ix(0, j, t) for t in range(4)]
            w, a, b = [ix(t, j, r) for t in [3, 4, 5]]
            yield [-o[0], -w, a]
            yield [-o[0], -w, b]
            yield [-o[0], w, -a, -b]
            yield [-o[1], w, -a]
            yield [-o[1], w, -b]
            yield [-o[1], -w, a, b]
            yield [-o[2], w]
            yield [-o[3], w, a]
            yield [-o[3], -w, -a]
    # fOutAlo
    yield [ix(6, 0, k) for k in range(n+s+1)]
    # fOutEq
    for r in rows:
        for k in range(n+s+1):
            select = ix(6, 0, k)
            if k < n:
                if bool(r >> k & 1) != value(r):
                    yield [-select]
            elif k < n+s:
                yield [-select, lit(3, k-n, r, value(r))]
            elif value(r):
                yield [-select]
    # fOut
    if s:
        yield [ix(6, 0, n+s-1), ix(7, s-1, 0)]
    # fPad
    for j in range(s):
        pad, true, a, b = ix(7,j,0), ix(0,j,2), ix(1,j,n+j), ix(2,j,n+j)
        yield [-pad, true]
        yield [-pad, a]
        yield [-pad, b]
        yield [pad, -true]
        yield [pad, -a]
        yield [pad, -b]
    # fPre
    for j in range(max(0,s-1)):
        yield [-ix(7,j+1,0), ix(7,j,0)]
    # fPadRd
    for j in range(s):
        for i in range(j):
            yield [-ix(7,i,0), -ix(1,j,n+i)]
            yield [-ix(7,i,0), -ix(2,j,n+i)]
    # fOrd
    for j in range(s):
        for k in range(n+j+1):
            for ell in range(k+1):
                yield [-ix(1,j,k), -ix(2,j,ell), ix(7,j,0)] + ([ix(0,j,3)] if ell == k else [])
    # fUsed
    for j in range(max(0,s-1)):
        yield ([ix(1,j+1+t,n+j) for t in range(s-1-j)] +
               [ix(2,j+1+t,n+j) for t in range(s-1-j)] + [ix(7,j,0)])
    # fNot
    for j in range(s):
        for k in range(n+j+1):
            yield [-ix(0,j,3), -ix(1,j,k), ix(2,j,k)]
    # fNotNot
    for j in range(s):
        for i in range(j):
            yield [-ix(0,j,3), -ix(0,i,3), -ix(1,j,n+i)]
    # fLex
    for j in range(max(0,s-1)):
        base = [ix(7,j,0), ix(1,j+1,n+j), ix(2,j+1,n+j)]
        for a in range(n+j+1):
            for b in range(a):
                yield [-ix(1,j,a), -ix(1,j+1,b)] + base
            for c in range(n+j+1):
                for d in range(c):
                    yield [-ix(1,j,a), -ix(1,j+1,a), -ix(2,j,c), -ix(2,j+1,d)] + base
                common = [-ix(1,j,a), -ix(1,j+1,a), -ix(2,j,c), -ix(2,j+1,c)]
                yield common + [-ix(0,j,1)] + base
                yield common + [-ix(0,j+1,0)] + base


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--n', type=int, default=14)
    p.add_argument('--gates', type=int, default=24)
    p.add_argument('--edges', required=True, type=Path)
    p.add_argument('--negative-rows', required=True, type=Path)
    p.add_argument('--out', required=True, type=Path)
    args = p.parse_args()
    edges = json.loads(args.edges.read_text())
    negatives = json.loads(args.negative_rows.read_text())
    assert isinstance(edges,list) and all(isinstance(e,list) and len(e)==2 for e in edges)
    assert isinstance(negatives,list) and all(isinstance(r,int) for r in negatives)
    target = lambda r: any((r >> a & 1) and (r >> b & 1) for a,b in edges)
    assert all(0 <= r < 2**args.n and not target(r) for r in negatives)
    positives = [(1<<a)|(1<<b) for a,b in edges]
    rows = sorted(set(negatives + positives))
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/'rows.json').write_text(json.dumps(rows)+'\n')
    # Stream the formula and retain exact original variable numbering.
    tmp = args.out/'clauses.tmp'
    used = set()
    count = 0
    with tmp.open('w') as f:
        for clause in clauses(args.n,args.gates,edges,rows):
            assert clause and all(x != 0 for x in clause)
            used.update(map(abs,clause))
            f.write(' '.join(map(str,clause))+' 0\n')
            count += 1
    cnf = args.out/'official.cnf'
    with cnf.open('wb') as dest, tmp.open('rb') as src:
        dest.write(f'p cnf {max(used)} {count}\n'.encode())
        while block := src.read(1024*1024): dest.write(block)
    tmp.unlink()
    digest = hashlib.sha256(cnf.read_bytes()).hexdigest()
    metadata = {'encoding':'PEqualNP.Library.LRAT.LinkN.enc2','n':args.n,'gates':args.gates,
                'negative_rows':len(set(negatives)),'positive_rows':len(set(positives)),
                'total_rows':len(rows),'clauses':count,'max_variable':max(used),
                'used_variables':len(used),'bytes':cnf.stat().st_size,'sha256':digest,
                'literal_map':'DIMACS d > 0 maps to Lean 2*d; -d maps to Lean 2*d+1',
                'op_codes':{'AND':0,'OR':1,'TRUE':2,'NOT':3},
                'semantic_warning':'SAT must be validated on all assignments; UNSAT suffices for the subset via link2'}
    (args.out/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps(metadata,indent=2))


if __name__ == '__main__':
    main()
