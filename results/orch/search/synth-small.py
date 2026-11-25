import argparse
import itertools
import json
import pathlib
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument('case', choices=['c6', 'c8', 'path6', 'star4', 'b3', 'b34', 'tetra', 'pendant3', 'fano'])
parser.add_argument('gates', type=int)
parser.add_argument('--seconds', type=int, default=120)
parser.add_argument('--mask', type=int, default=0)
parser.add_argument('--or-max', type=int)
parser.add_argument('--boundary', action='store_true')
parser.add_argument('--canonical-order', action='store_true')
parser.add_argument('--output-dir', default='/tmp/oec/pequalnp-pilot-58')
parser.add_argument('--solver', default='/tmp/oec/pequalnp-pilot-58/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical')
parser.add_argument('--emit-only', action='store_true')
args = parser.parse_args()
cases = {
    'c6': (3, 3, [(0, 0), (0, 1), (1, 1), (1, 2), (2, 2), (2, 0)]),
    'c8': (4, 4, [(i, j) for i in range(4) for j in (i, (i+1) % 4)]),
    'path6': (3, 3, [(0, 0), (1, 0), (1, 1), (2, 1), (2, 2)]),
    'star4': (1, 3, [(0, j) for j in range(3)]),
    'b3': (3, 3, [(p,l) for p in range(3) for l in range(3) if args.mask & (1 << (3*p+l))]),
    'b34': (3, 4, [(p,l) for p in range(3) for l in range(4) if args.mask & (1 << (4*p+l))]),
    'tetra': (4, 6, [(p,l) for l,e in enumerate(itertools.combinations(range(4),2)) for p in e]),
    'pendant3': (3, 6, [(p,l) for p in range(3) for l in (p,(p+1)%3,p+3)]),
    'fano': (7, 7, [(p,l) for l in range(7) for p in (l,(l+1)%7,(l+3)%7)]),
}
np, nl, edges = cases[args.case]
n = np + nl
k = args.gates
count = 0
clauses = []

def var():
    global count
    count += 1
    return count

def add(*lits):
    if True in [x for x in lits if type(x) is bool]:
        return
    row = [x for x in lits if type(x) is not bool]
    if any(-x in row for x in row):
        return
    clauses.append(list(dict.fromkeys(row)))

def neg(lit):
    return not lit if type(lit) is bool else -lit

def onehot(xs):
    add(*xs)
    for a, b in itertools.combinations(xs, 2):
        add(-a, -b)

assignments = list(range(1 << n))
if args.boundary:
    edge_masks = [(1 << p) | (1 << (np+l)) for p,l in edges]
    independent = lambda t: not any(t & e == e for e in edge_masks)
    maximal = [t for t in assignments if independent(t) and all(
        not independent(t | (1 << i)) for i in range(n) if not t & (1 << i))]
    assignments = sorted(set(edge_masks + maximal))
vals = [[bool((t >> i) & 1) for t in assignments] for i in range(n)]
selectors = []
for g in range(k):
    op = var()
    left = [var() for _ in vals]
    right = [var() for _ in vals]
    onehot(left)
    onehot(right)
    for a in range(n+g):
        for b in range(a):
            add(-left[a], -right[b])
    out = []
    for t in range(len(assignments)):
        a, b, y = var(), var(), var()
        for i in range(n+g):
            value = vals[i][t]
            add(-left[i], neg(value), a)
            add(-left[i], value, -a)
            add(-right[i], neg(value), b)
            add(-right[i], value, -b)
        add(-op, -a, -b, y)
        add(-op, a, -y)
        add(-op, b, -y)
        add(op, a, b, -y)
        add(op, -a, y)
        add(op, -b, y)
        out.append(y)
    vals.append(out)
    selectors.append((op, left, right))
for ti,t in enumerate(assignments):
    target = any(((t >> p) & 1) and ((t >> (np+l)) & 1) for p,l in edges)
    add(vals[-1][ti] if target else -vals[-1][ti])
if args.or_max is not None:
    for gate_set in itertools.combinations(selectors, args.or_max + 1):
        add(*(gate[0] for gate in gate_set))
if args.canonical_order:
    for g in range(k-1):
        op, left, right = selectors[g]
        op1, left1, right1 = selectors[g+1]
        dependency = right1[n+g]
        for a in range(n+g):
            for b in range(a):
                add(-left[a], -left1[b], dependency)
            for ra in range(a,n+g):
                for rb in range(a,ra):
                    add(-left[a], -left1[a], -right[ra], -right1[rb], dependency)
                add(-left[a], -left1[a], -right[ra], -right1[ra], -op, op1, dependency)
    for g in range(k-1):
        readers=[]
        for h in range(g+1,k):
            readers.extend((selectors[h][1][n+g], selectors[h][2][n+g]))
        add(*readers)

base = pathlib.Path(args.output_dir)
base.mkdir(parents=True, exist_ok=True)
stem = f'synth-{args.case}-{k}'
if args.case in ('b3', 'b34'):
    stem += f'-m{args.mask}'
if args.or_max is not None:
    stem += f'-or{args.or_max}'
if args.boundary:
    stem += '-boundary'
if args.canonical_order:
    stem += '-canonical'
cnf = base / (stem + '.cnf')
with cnf.open('w') as f:
    f.write(f'p cnf {count} {len(clauses)}\n')
    for row in clauses:
        f.write(' '.join(map(str, row))+' 0\n')
if args.emit_only:
    print(json.dumps({'cnf': str(cnf), 'variables': count, 'clauses': len(clauses)}), flush=True)
    raise SystemExit(0)
solver = args.solver
start = time.monotonic()
with (base / (stem + '.solver.log')).open('w') as log:
    r = subprocess.run([solver, '-t', str(args.seconds), str(cnf)], stdout=log, stderr=subprocess.STDOUT)
summary = {'case':args.case,'n':n,'edges':edges,'gates':k,'variables':count,'clauses':len(clauses),
           'returncode':r.returncode,'seconds':time.monotonic()-start,'boundary':args.boundary,'rows':len(assignments),
           'canonical_order':args.canonical_order}
if args.or_max is not None:
    summary['or_max'] = args.or_max
if r.returncode == 10:
    model = set()
    for line in (base / (stem + '.solver.log')).read_text().splitlines():
        if line.startswith('v '):
            model.update(int(x) for x in line.split()[1:] if int(x)>0)
    circuit=[]
    for op,left,right in selectors:
        circuit.append(('and' if op in model else 'or', next(i for i,s in enumerate(left) if s in model),
                        next(i for i,s in enumerate(right) if s in model)))
    for t in range(1 << n):
        wires=[bool((t>>i)&1) for i in range(n)]
        for op,a,b in circuit:
            wires.append((wires[a] and wires[b]) if op=='and' else (wires[a] or wires[b]))
        expected=any(((t>>p)&1) and ((t>>(np+l))&1) for p,l in edges)
        assert wires[-1] == expected
    summary['circuit']=circuit
    summary['independent_truth_table_check']=True
(base / (stem+'.json')).write_text(json.dumps(summary,indent=2))
print(json.dumps(summary),flush=True)
