import argparse
import json
import sys
import time
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--z3-python', required=True)
parser.add_argument('--side', type=int, required=True)
parser.add_argument('--gates', type=int, required=True)
parser.add_argument('--no-read2', action='store_true')
parser.add_argument('--read-bound', type=int, choices=(1,2), default=2)
parser.add_argument('--critical-rows', action='store_true')
parser.add_argument('--engine', choices=('smt','qfbv'), default='smt')
parser.add_argument('--timeout-ms', type=int, default=240000)
parser.add_argument('--output', required=True)
args = parser.parse_args()
sys.path.insert(0, args.z3_python)
import z3

P = L = args.side
n = P + L
edges = [(p, P + l) for p in range(P) for l in range(L) if l in (p, (p + 1) % L)]
def graph_value(x):
    return any(((x >> p) & 1) and ((x >> l) & 1) for p,l in edges)
assignments = list(range(1 << n))
if args.critical_rows:
    positive = {(1 << p) | (1 << l) for p,l in edges}
    negative = {x for x in assignments if not graph_value(x) and all(graph_value(x | (1 << i)) for i in range(n) if not ((x >> i) & 1))}
    assignments = sorted(positive | negative)
rows = len(assignments)
input_tables = [sum(1 << j for j,x in enumerate(assignments) if (x >> i) & 1) for i in range(n)]
target = 0
for p, l in edges:
    target |= input_tables[p] & input_tables[l]

solver = z3.SolverFor('QF_BV') if args.engine == 'qfbv' else z3.Solver()
solver.set(timeout=args.timeout_ms)
solver.set(max_memory=4096)
tables = [z3.BitVecVal(x, rows) for x in input_tables]
selectors = []
operations = []
counts = [(a,b) for a in range(3) for b in range(3) if a+b]
vectors = [[z3.BoolVal((i == 0 and c == (1,0)) or (i == P and c == (0,1))) for c in counts] for i in range(n)]

for j in range(args.gates):
    size = n+j
    left = [z3.Bool(f'left_{j}_{i}') for i in range(size)]
    right = [z3.Bool(f'right_{j}_{i}') for i in range(size)]
    op = z3.Bool(f'is_or_{j}')
    selectors.append((left,right))
    operations.append(op)
    solver.add(z3.PbEq([(x,1) for x in left],1), z3.PbEq([(x,1) for x in right],1))
    for a in range(size):
        for b in range(a+1):
            solver.add(z3.Or(z3.Not(left[a]), z3.Not(right[b])))
    def select_table(choices):
        value = z3.BitVecVal(0, rows)
        for choice, table in zip(choices,tables):
            value = value | z3.If(choice,table,z3.BitVecVal(0,rows))
        return value
    lhs, rhs = select_table(left), select_table(right)
    table = z3.BitVec(f'function_{j}',rows)
    solver.add(table == z3.If(op,lhs | rhs,lhs & rhs))
    for earlier in tables:
        solver.add(table != earlier)
    if j:
        solver.add(z3.Implies(z3.Not(z3.Or(left[-1],right[-1])),z3.ULT(tables[-1],table)))
    tables.append(table)

    if args.no_read2:
        def select_vector(choices):
            return [z3.Or(*[z3.And(choice,vector[k]) for choice,vector in zip(choices,vectors)]) for k in range(len(counts))]
        a,b = select_vector(left), select_vector(right)
        value = []
        for k,(cp,cl) in enumerate(counts):
            both = z3.Or(*[z3.And(a[i],b[h]) for i,(ap,al) in enumerate(counts) for h,(bp,bl) in enumerate(counts) if ap+bp == cp and al+bl == cl])
            bit = z3.Bool(f'read_{j}_{cp}_{cl}')
            solver.add(bit == z3.If(op,z3.Or(a[k],b[k]),both))
            value.append(bit)
        vectors.append(value)

for j in range(args.gates-1):
    solver.add(z3.Or(*[side[n+j] for pair in selectors[j+1:] for side in pair]))
solver.add(tables[-1] == z3.BitVecVal(target,rows))
if args.no_read2:
    for k,(p,l) in enumerate(counts):
        if 0 < p <= args.read_bound and 0 < l <= args.read_bound:
            solver.add(z3.Not(vectors[-1][k]))

prefix = Path(args.output)
prefix.with_suffix('.source.py').write_text(Path(__file__).read_text())
prefix.with_suffix('.smt2').write_text(solver.to_smt2())
print(json.dumps({'side':P,'gates':args.gates,'forbidden_read_bound':args.read_bound if args.no_read2 else None,'distinguished_edge':[0,P] if args.no_read2 else None,'truth_rows':rows,'critical_rows':args.critical_rows,'timeout_ms':args.timeout_ms,'solver':z3.get_version_string(),'engine':args.engine,'clauses':len(solver.assertions())}),flush=True)
start=time.monotonic()
result=solver.check()
print('result',result,'seconds',time.monotonic()-start,flush=True)
print(solver.statistics(),flush=True)
if result==z3.sat:
    model=solver.model()
    gates=[]
    for (left,right),op in zip(selectors,operations):
        a=next(i for i,x in enumerate(left) if z3.is_true(model.eval(x)))
        b=next(i for i,x in enumerate(right) if z3.is_true(model.eval(x)))
        gates.append(['or' if z3.is_true(model.eval(op)) else 'and',a,b])
    print('gates',json.dumps(gates),flush=True)
    tt=list(input_tables)
    vv=[{(1,0)} if i==0 else {(0,1)} if i==P else set() for i in range(n)]
    for op,a,b in gates:
        tt.append(tt[a]|tt[b] if op=='or' else tt[a]&tt[b])
        vv.append(vv[a]|vv[b] if op=='or' else {(min(3,p+q),min(3,l+m)) for p,l in vv[a] for q,m in vv[b]})
    check=tt[-1]==target
    full_check=True
    for x in range(1 << n):
        values=[bool((x >> i) & 1) for i in range(n)]
        for op,a,b in gates:
            values.append(values[a] or values[b] if op=='or' else values[a] and values[b])
        if values[-1] != graph_value(x):
            full_check=False
    read2=any(p<=args.read_bound and l<=args.read_bound for p,l in vv[-1])
    print('independent_function_check',check,'full_function_check',full_check,'edge_reads_at_most',args.read_bound,read2,'vectors',sorted(vv[-1]),flush=True)
    assert check and full_check
    assert not args.no_read2 or not read2
    prefix.with_suffix('.model.json').write_text(json.dumps({'P':P,'L':L,'edges':edges,'gates':gates,'output':n+len(gates)-1,'read_bound':args.read_bound,'reads_at_most_bound':read2},indent=2)+'\n')
elif result==z3.unknown:
    print('reason_unknown',solver.reason_unknown(),flush=True)
