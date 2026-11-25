"""Exact bounded-OR synthesis with unrestricted free AND gates.

Each OR operand and the output is an arbitrary AND of inputs, a free false
constant, and previous OR outputs. Empty AND represents true. Collapse all
AND-only regions to represent every AO circuit with <=k ORs; pad missing ORs
by false OR false. Both constants are free, and singleton constraints on AND
nodes are deliberately omitted. These choices enlarge the searched class,
so UNSAT remains a valid OR-count lower bound for posted circuits.
"""
import argparse
import itertools
import json
import resource
import subprocess
import time
from pathlib import Path

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--N', type=int, required=True)
ap.add_argument('--mask', type=int, required=True)
ap.add_argument('--ors', type=int, required=True)
ap.add_argument('--seconds', type=int, default=120)
ap.add_argument('--full', action='store_true', help='encode all assignments, not only critical rows')
ap.add_argument('--solve', action='store_true', help='run solver; default only prepares CNF')
ap.add_argument('--solver', type=Path, default=Path('/tmp/oec/pequalnp-pilot-53/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'))
ap.add_argument('--outdir', type=Path, required=True)
a = ap.parse_args()
assert 1 <= a.N <= 8
assert a.ors >= 0
assert 0 <= a.mask < (1 << (a.N * a.N))
assert a.seconds > 0
n = 2*a.N
edges = [(p,a.N+l) for p in range(a.N) for l in range(a.N) if a.mask >> (p*a.N+l) & 1]
def expected(r):
    return any((r >> p & 1) and (r >> l & 1) for p,l in edges)
c4free = all(not all((p,a.N+l) in edges for p in ps for l in ls)
             for ps in itertools.combinations(range(a.N),2)
             for ls in itertools.combinations(range(a.N),2))
if a.full:
    assignments = list(range(1 << n))
else:
    aset = {1 << i for i in range(n)}
    aset.update((1 << p) | (1 << l) for p,l in edges)
    aset.update(r for r in range(1 << n) if not expected(r)
                and all(expected(r | (1 << i)) for i in range(n) if not (r >> i & 1)))
    assignments = sorted(aset)
clauses = []
nv = 0
def var():
    global nv
    nv += 1
    return nv
def neg(x):
    return not x if isinstance(x,bool) else -x
def clause(*xs):
    if any(isinstance(x,bool) and x for x in xs):
        return
    vals = [x for x in xs if not isinstance(x,bool)]
    assert all(isinstance(x,int) and x != 0 for x in vals)
    clauses.append(vals)
def and_term(x,y):
    if isinstance(x,bool):
        return y if x else False
    if isinstance(y,bool):
        return x if y else False
    z = var()
    clause(-z,x)
    clause(-z,y)
    clause(z,-x,-y)
    return z
def equivalent_or(z,terms):
    for t in terms:
        clause(neg(t),z)
    clause(-z,*terms)
def selected_or(selectors,truth_row):
    terms = [and_term(s,t) for s,t in zip(selectors,truth_row)]
    z = var()
    equivalent_or(z,terms)
    return z
def selected_and(selectors,truth_row):
    return neg(selected_or(selectors,[neg(t) for t in truth_row]))
truth = [[bool(r >> i & 1) for r in assignments] for i in range(n)]
truth.append([False for r in assignments])
gates = []
for j in range(a.ors):
    ss = [[var() for i in range(n+1+j)] for side in range(2)]
    gv = []
    for ri,r in enumerate(assignments):
        row = [col[ri] for col in truth]
        av = selected_and(ss[0],row)
        bv = selected_and(ss[1],row)
        g = var()
        equivalent_or(g,[av,bv])
        gv.append(g)
    gates.append({'selectors':ss,'truth':gv})
    truth.append(gv)
output_selectors = [var() for i in range(n+1+a.ors)]
for ri,r in enumerate(assignments):
    out = selected_and(output_selectors,[col[ri] for col in truth])
    clause(out if expected(r) else -out)

stem = f'free-and-n{a.N}-m{a.mask}-or{a.ors}-' + ('full' if a.full else 'critical')
a.outdir.mkdir(parents=True,exist_ok=True)
cnf = a.outdir/(stem+'.cnf')
with cnf.open('w') as f:
    f.write(f'p cnf {nv} {len(clauses)}\n')
    for c in clauses:
        f.write(' '.join(map(str,c))+' 0\n')
mapping = {'N':a.N,'mask':a.mask,'ors':a.ors,'c4free':c4free,'edges':edges,
           'assignments':assignments,'gates':gates,'output_selectors':output_selectors,
           'variables':nv,'clauses':len(clauses),
           'completeness':'arbitrary AND subsets; free constants; false OR padding; no singleton constraints; no symmetry/usefulness assumptions'}
(a.outdir/(stem+'.mapping.json')).write_text(json.dumps(mapping,indent=2)+'\n')
print(json.dumps({'stem':stem,'rows':len(assignments),'variables':nv,'clauses':len(clauses),'c4free':c4free}),flush=True)
if not a.solve:
    raise SystemExit(0)

def limit():
    resource.setrlimit(resource.RLIMIT_AS,(256*1024*1024,256*1024*1024))
sol = a.outdir/(stem+'.sol')
sol.unlink(missing_ok=True)
start = time.monotonic()
with (a.outdir/(stem+'.solver.stdout')).open('w') as stdout, (a.outdir/(stem+'.solver.stderr')).open('w') as stderr:
    try:
        run = subprocess.run([str(a.solver),'-t',str(a.seconds),'-w',str(sol),str(cnf)],
                             stdout=stdout,stderr=stderr,preexec_fn=limit,timeout=a.seconds+5)
        code = run.returncode
    except subprocess.TimeoutExpired:
        code = 'wall_timeout'
solution = sol.read_text() if sol.exists() else ''
status = 'UNKNOWN'
result = {'stem':stem,'elapsed_seconds':time.monotonic()-start,'solver_returncode':code,
          'N':a.N,'mask':a.mask,'ors':a.ors,'c4free':c4free}
if code == 20 and solution.startswith('s UNSATISFIABLE'):
    status = 'UNSAT'
elif code == 10 and solution.startswith('s SATISFIABLE'):
    vals = {int(tok) for line in solution.splitlines() if line.startswith('v ')
            for tok in line[2:].split() if int(tok)>0}
    selected = [[[i for i,s in enumerate(side) if s in vals] for side in g['selectors']] for g in gates]
    output = [i for i,s in enumerate(output_selectors) if s in vals]
    errors = []
    for r in range(1 << n):
        ws = [bool(r >> i & 1) for i in range(n)] + [False]
        for j,(left,right) in enumerate(selected):
            v = all(ws[i] for i in left) or all(ws[i] for i in right)
            ws.append(v)
        actual = all(ws[i] for i in output)
        if actual != expected(r):
            errors.append(r)
    assert not errors, errors
    status = 'SAT: independently verified on all assignments'
    result['gates'] = selected
    result['output'] = output
    result['verified_assignments'] = 1 << n
    (a.outdir/(stem+'.witness.json')).write_text(json.dumps(result,indent=2)+'\n')
result['status'] = status
(a.outdir/(stem+'.result.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
