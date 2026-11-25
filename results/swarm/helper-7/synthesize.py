#!/usr/bin/env python3
"""Exact boundary-row SAT synthesis of monotone fan-in-two graph circuits."""
import argparse
import itertools
import json
from pathlib import Path
import subprocess
import shutil
import time

ROOT = Path(__file__).resolve().parent
DEFAULT_SOLVER = shutil.which('kissat')

class CNF:
    def __init__(self):
        self.nvars = 0
        self.clauses = []
    def var(self):
        self.nvars += 1
        return self.nvars
    def add(self, *lits):
        self.clauses.append(list(lits))
    def one(self, xs):
        self.add(*xs)
        for a, b in itertools.combinations(xs, 2):
            self.add(-a, -b)
    def write(self, filename):
        with open(filename, 'w') as out:
            out.write(f'p cnf {self.nvars} {len(self.clauses)}\n')
            for clause in self.clauses:
                out.write(' '.join(map(str, clause)) + ' 0\n')

def graph_info(n, edges):
    edges = sorted(set(tuple(sorted(e)) for e in edges))
    assert all(0 <= u < v < n for u, v in edges)
    edge_masks = [(1 << u) | (1 << v) for u, v in edges]
    independent = [x for x in range(1 << n) if not any(x & e == e for e in edge_masks)]
    independent_set = set(independent)
    maximal = [x for x in independent if all(x & (1 << i) or (x | (1 << i)) not in independent_set for i in range(n))]
    tau = n - max(map(int.bit_count, independent), default=0)
    rows = [(x, True) for x in edge_masks] + [(x, False) for x in maximal]
    return {'n': n, 'edges': edges, 'tau': tau, 'standard_bound': len(edges) + tau - 1 if edges else 0, 'rows': rows}

def first_pair_symmetry(info, node_limit=1000000):
    n = info['n']
    adjacency = [[False] * n for _ in range(n)]
    for a, b in info['edges']:
        adjacency[a][b] = adjacency[b][a] = True
    degree = list(map(sum, adjacency))
    pairs = list(itertools.combinations(range(n), 2))
    parent = {p:p for p in pairs}
    def find(p):
        while parent[p] != p:
            parent[p] = parent[parent[p]]
            p = parent[p]
        return p
    def union(a,b):
        a,b=find(a),find(b)
        if a != b:
            if (a[1],a[0]) > (b[1],b[0]): a,b=b,a
            parent[b]=a
    mapping = [-1] * n
    used = [False] * n
    nodes = 0
    autos = []
    def search(depth):
        nonlocal nodes
        nodes += 1
        if nodes > node_limit:
            return
        if depth == n:
            assert sorted(mapping) == list(range(n))
            assert all(adjacency[a][b] == adjacency[mapping[a]][mapping[b]] for a,b in pairs)
            autos.append(mapping.copy())
            for a,b in pairs:
                union((a,b),tuple(sorted((mapping[a],mapping[b]))))
            return
        best = None
        for v in range(n):
            if mapping[v] >= 0: continue
            possible = [w for w in range(n) if not used[w] and degree[v] == degree[w]
                        and all(adjacency[v][u] == adjacency[w][mapping[u]]
                                for u in range(n) if mapping[u] >= 0)]
            if not possible: return
            if best is None or len(possible) < len(best[1]):
                best=(v,possible)
        v,possible=best
        for w in possible:
            mapping[v]=w; used[w]=True
            search(depth+1)
            mapping[v]=-1; used[w]=False
            if nodes > node_limit: break
    search(0)
    reps=sorted({find(p) for p in pairs},key=lambda p:(p[1],p[0]))
    return {'representatives':reps,'automorphisms':autos,'nodes':nodes,'truncated':nodes > node_limit}

def encode(info, k, normalized=True, symmetry=None, distinct=False, undominated=False, oriented=False):
    n, rows = info['n'], info['rows']
    assert k >= 1 and info['edges'], 'positive-size nonempty graph only'
    f = CNF()
    left = [[f.var() for _ in range(n+j)] for j in range(k)]
    right = [[f.var() for _ in range(n+j)] for j in range(k)]
    op = [f.var() for _ in range(k)]  # true means AND, false OR
    pad = [f.var() for _ in range(k)]
    lv = [[f.var() for _ in rows] for _ in range(k)]
    rv = [[f.var() for _ in rows] for _ in range(k)]
    val = [[f.var() for _ in rows] for _ in range(k)]
    f.add(-pad[0])
    for v in sorted({v for edge in info['edges'] for v in edge}):
        f.add(*(selector for j in range(k) for selector in (left[j][v],right[j][v])))
    if symmetry is not None:
        reps=set(map(tuple,symmetry['representatives']))
        for a,b in itertools.combinations(range(n),2):
            if (a,b) not in reps:
                f.add(-left[0][a],-right[0][b])
    for j in range(k):
        f.one(left[j]); f.one(right[j])
        if j:
            f.add(-pad[j-1], pad[j])
            f.add(-pad[j], left[j][n+j-1])
            f.add(-pad[j], right[j][n+j-1])
        for a in range(n+j):
            for b in range(a+1):
                f.add(pad[j], -left[j][a], -right[j][b])
        for r, (mask, _) in enumerate(rows):
            for selectors, value in [(left[j], lv[j][r]), (right[j], rv[j][r])]:
                for s, selector in enumerate(selectors):
                    if s < n:
                        f.add(-selector, value if mask & (1 << s) else -value)
                    else:
                        source_value = val[s-n][r]
                        f.add(-selector, -value, source_value)
                        f.add(-selector, value, -source_value)
            a, l, h, y = op[j], lv[j][r], rv[j][r], val[j][r]
            f.add(-a, -l, -h, y)
            f.add(-a, l, -y)
            f.add(-a, h, -y)
            f.add(a, l, h, -y)
            f.add(a, -l, y)
            f.add(a, -h, y)
        if distinct or undominated:
            for source in range(n+j):
                if source < n:
                    if undominated:
                        differences=[val[j][r] if target else -val[j][r]
                                     for r,(mask,target) in enumerate(rows)
                                     if bool(mask & (1 << source)) != target]
                    else:
                        differences=[-val[j][r] if mask & (1 << source) else val[j][r]
                                     for r,(mask,_) in enumerate(rows)]
                else:
                    differences=[f.var() for _ in rows]
                    for r,d in enumerate(differences):
                        x,y=val[j][r],val[source-n][r]
                        if undominated:
                            positive=rows[r][1]
                            f.add(-d,x if positive else -x)
                            f.add(-d,-y if positive else y)
                        else:
                            f.add(-d,x,y); f.add(-d,-x,-y)
                f.add(pad[j],*differences)
        if normalized:
            # A real gate may be folded to false if false on all positive rows,
            # or folded to true if true on all maximal-negative rows.
            f.add(pad[j],*(val[j][r] for r,(_,target) in enumerate(rows) if target))
            f.add(pad[j],*(-val[j][r] for r,(_,target) in enumerate(rows) if not target))
            if j == 0:
                edges=set(map(tuple,info['edges']))
                for a,b in itertools.combinations(range(n),2):
                    if (a,b) not in edges:
                        f.add(-op[j],-left[j][a],-right[j][b])
            # Any gate redundant on all boundary rows can be replaced and removed.
            # The remaining two operands are incomparable on those rows.
            lo = [f.var() for _ in rows]
            hi = [f.var() for _ in rows]
            f.add(pad[j], *lo)
            f.add(pad[j], *hi)
            for r in range(len(rows)):
                f.add(-lo[r], lv[j][r]); f.add(-lo[r], -rv[j][r])
                f.add(-hi[r], -lv[j][r]); f.add(-hi[r], rv[j][r])
                if oriented:
                    allowed=-op[j] if rows[r][1] else op[j]
                    f.add(-lo[r],allowed); f.add(-hi[r],allowed)
            # Non-output real gates have a consumer; pads consume the last real gate.
            if j < k-1:
                consumers = [x for i in range(j+1, k) for x in (left[i][n+j], right[i][n+j])]
                f.add(pad[j], *consumers)
            # Kahn ordering by the maximum predecessor index removes order symmetry.
            if j:
                for a in range(n+j-1):
                    for b in range(a):
                        f.add(-right[j-1][a], -right[j][b])
    for r, (_, target) in enumerate(rows):
        f.add(val[-1][r] if target else -val[-1][r])
    return f, {'left':left, 'right':right, 'op':op, 'pad':pad, 'val':val}

def decode(text, mapping):
    positive = set()
    for line in text.splitlines():
        if line.startswith('v '):
            positive.update(int(t) for t in line.split()[1:] if int(t) > 0)
    result = []
    for j, (ls, rs, o, p) in enumerate(zip(mapping['left'], mapping['right'], mapping['op'], mapping['pad'])):
        l = [i for i, v in enumerate(ls) if v in positive]
        r = [i for i, v in enumerate(rs) if v in positive]
        assert len(l) == len(r) == 1
        result.append({'op':'and' if o in positive else 'or', 'left':l[0], 'right':r[0], 'pad':p in positive})
    return result

def verify(info, gates):
    n, edges = info['n'], info['edges']
    for mask in range(1 << n):
        values = [bool(mask & (1 << i)) for i in range(n)]
        for g in gates:
            assert 0 <= g['left'] < len(values) and 0 <= g['right'] < len(values)
            a, b = values[g['left']], values[g['right']]
            values.append(a and b if g['op'] == 'and' else a or b)
        expected = any(mask & (1 << a) and mask & (1 << b) for a, b in edges)
        assert values[-1] == bool(expected), (mask, values[-1], expected)
    return {'truth_rows_checked': 1 << n, 'actual_gates': sum(not g['pad'] for g in gates)}

def run(info, name, k, seconds, normalized=True, seed=0, solver=DEFAULT_SOLVER, symmetry=False, distinct=False, undominated=False, oriented=False):
    if solver is None:
        raise ValueError('Kissat was not found; provide --solver PATH')
    stamp = f'{name}-k{k}-' + ('norm' if normalized else 'plain') + ('-sym' if symmetry else '') + ('-distinct' if distinct else '') + ('-undominated' if undominated else '') + ('-oriented' if oriented else '') + f'-s{seed}-{time.time_ns()}'
    directory = ROOT / 'synthesis' / stamp
    directory.mkdir(parents=True, exist_ok=True)
    symmetry_data=first_pair_symmetry(info) if symmetry else None
    f, mapping = encode(info, k, normalized, symmetry_data, distinct, undominated, oriented)
    f.write(directory/'input.cnf')
    (directory/'encoding.json').write_text(json.dumps({'info':info,'mapping':mapping,'normalized':normalized,'symmetry':symmetry_data,'distinct':distinct,'undominated':undominated,'oriented':oriented},indent=2))
    started = time.monotonic()
    with (directory/'solver.stdout').open('w') as out, (directory/'solver.stderr').open('w') as err:
        process = subprocess.Popen([str(solver), f'--time={seconds}', f'--seed={seed}', str(directory/'input.cnf')], stdout=out, stderr=err)
        print(json.dumps({'event':'started','pid':process.pid,'graph':name,'k':k,'directory':str(directory)}),flush=True)
        process.wait()
    result = {'graph':name,'k':k,'normalized':normalized,'exit':process.returncode,'seconds':time.monotonic()-started,'vars':f.nvars,'clauses':len(f.clauses),'directory':str(directory)}
    stdout = (directory/'solver.stdout').read_text()
    if process.returncode == 10:
        assert 's SATISFIABLE' in stdout
        result['status']='SAT'
        result['gates']=decode(stdout,mapping)
        result.update(verify(info,result['gates']))
    elif process.returncode == 20:
        assert 's UNSATISFIABLE' in stdout
        result['status']='UNSAT'
    else:
        result['status']='UNKNOWN'
    (directory/'result.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result),flush=True)
    return result

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--graph',default='C4')
    ap.add_argument('--k',type=int)
    ap.add_argument('--solver',type=Path,default=DEFAULT_SOLVER)
    ap.add_argument('--graph-file',type=Path)
    ap.add_argument('--seconds',type=int,default=60)
    ap.add_argument('--plain',action='store_true')
    ap.add_argument('--symmetry',action='store_true')
    ap.add_argument('--distinct',action='store_true')
    ap.add_argument('--undominated',action='store_true')
    ap.add_argument('--oriented',action='store_true')
    ap.add_argument('--seed',type=int,default=0)
    ap.add_argument('--candidates',type=Path,default=ROOT/'candidates.json')
    args=ap.parse_args()
    if args.solver is None:
        ap.error('Kissat was not found; provide --solver PATH')
    if args.plain and args.oriented:
        ap.error('--oriented requires normalization; omit --plain')
    if args.graph_file:
        g=json.loads(args.graph_file.read_text())
        n,edges=g['n'],g['edges']
        args.graph=g.get('name',args.graph_file.stem)
    elif (ROOT/'graphs'/f'{args.graph}.json').exists():
        g=json.loads((ROOT/'graphs'/f'{args.graph}.json').read_text())
        n,edges=g['n'],g['edges']
    elif args.graph.startswith('C') and args.graph[1:].isdigit():
        n=int(args.graph[1:]); edges=[(i,(i+1)%n) for i in range(n)]
    else:
        candidates=json.loads(args.candidates.read_text())
        g=next(x for x in candidates if x['name']==args.graph)
        n,edges=g['n'],g['edges']
    info=graph_info(n,edges)
    k=args.k if args.k is not None else info['standard_bound']-1
    run(info,args.graph,k,args.seconds,not args.plain,args.seed,solver=args.solver,symmetry=args.symmetry,distinct=args.distinct,undominated=args.undominated,oriented=args.oriented)

if __name__ == '__main__': main()
