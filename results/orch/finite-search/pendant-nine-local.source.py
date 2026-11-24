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
parser.add_argument('--graph', choices=('cycle','theta','pendant'), default='cycle')
parser.add_argument('--two-dirty-cone', action='store_true')
parser.add_argument('--topform', action='store_true')
parser.add_argument('--max-dirty', type=int)
parser.add_argument('--local-irred', action='store_true')
parser.add_argument('--any-edge', action='store_true')
parser.add_argument('--timeout-ms', type=int, default=240000)
parser.add_argument('--output', required=True)
args = parser.parse_args()
sys.path.insert(0, args.z3_python)
import z3

P = args.side
L = args.side+1 if args.graph == 'pendant' else args.side
n = P + L
edges = [(p, P + l) for p in range(P) for l in range(L) if l in (p, (p + 1) % P)]
if args.graph == 'pendant':
    edges.append((0,P+P))
if args.graph == 'theta':
    if P != 4:
        raise ValueError('theta requires side 4')
    edges = [(0,4),(0,5),(0,6),(1,4),(1,7),(2,5),(2,7),(3,6),(3,7)]
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
chosen_values = []
counts = [(a,b) for a in range(3) for b in range(3) if a+b]
chosen_edges = [z3.Bool(f'chosen_edge_{i}') for i in range(len(edges))] if args.any_edge else []
if chosen_edges:
    solver.add(z3.PbEq([(x,1) for x in chosen_edges],1))
    vectors = [[z3.Or(*[x for x,e in zip(chosen_edges,edges) if (c == (1,0) and e[0] == i) or (c == (0,1) and e[1] == i)]) for c in counts] for i in range(n)]
else:
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
    chosen_values.append((lhs,rhs))
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
if args.local_irred:
    private=[]
    for i in range(args.gates):
        uses=[z3.Or(pair[0][n+i],pair[1][n+i]) for pair in selectors[i+1:]]
        private.append(z3.PbEq([(x,1) for x in uses],1) if uses else z3.BoolVal(False))
    for j,pair in enumerate(selectors):
        for slot in range(2):
            other=chosen_values[j][1-slot]
            for i in range(j):
                premise=z3.And(pair[slot][n+i],private[i],operations[i] == operations[j])
                for grandchild in chosen_values[i]:
                    replacement=z3.If(operations[j],grandchild | other,grandchild & other)
                    solver.add(z3.Implies(premise,replacement != tables[n+j]))
solver.add(tables[-1] == z3.BitVecVal(target,rows))
if args.no_read2:
    for k,(p,l) in enumerate(counts):
        if 0 < p <= args.read_bound and 0 < l <= args.read_bound:
            solver.add(z3.Not(vectors[-1][k]))

if args.two_dirty_cone or args.topform or args.max_dirty is not None:
    negative_mask = sum(1 << j for j,x in enumerate(assignments) if not graph_value(x))
    below = [(table & z3.BitVecVal(negative_mask,rows)) == 0 for table in tables[n:]]
    if args.max_dirty is not None:
        solver.add(z3.PbLe([(z3.And(z3.Not(op),z3.Not(b)),1) for op,b in zip(operations,below)],args.max_dirty))
    ancestor = []
    for j,(left,right) in enumerate(selectors):
        prev=[]
        for i in range(j):
            bit=z3.Bool(f'ancestor_{j}_{i}')
            paths=[left[n+i],right[n+i]]
            paths += [z3.And(z3.Or(left[n+h],right[n+h]),ancestor[h][i]) for h in range(i+1,j)]
            solver.add(bit == z3.Or(*paths))
            if args.topform or args.two_dirty_cone:
                solver.add(z3.Not(z3.And(z3.Not(operations[i]),below[i],z3.Not(operations[j]),bit)))
            prev.append(bit)
        ancestor.append(prev)
    if args.two_dirty_cone:
        witnesses=[]
        for j in range(2,args.gates):
            members=[z3.And(z3.Not(operations[i]),z3.Not(below[i]),ancestor[j][i]) for i in range(j)]
            witnesses.append(z3.And(z3.Not(operations[j]),below[j],z3.PbGe([(x,1) for x in members],2)))
        solver.add(z3.Or(*witnesses))

prefix = Path(args.output)
prefix.with_suffix('.source.py').write_text(Path(__file__).read_text())
prefix.with_suffix('.smt2').write_text(solver.to_smt2())
print(json.dumps({'graph':args.graph,'P':P,'L':L,'gates':args.gates,'forbidden_read_bound':args.read_bound if args.no_read2 else None,'distinguished_edge':'any' if args.any_edge else [0,P] if args.no_read2 else None,'two_dirty_cone':args.two_dirty_cone,'topform':args.topform,'max_dirty':args.max_dirty,'local_irred':args.local_irred,'truth_rows':rows,'critical_rows':args.critical_rows,'timeout_ms':args.timeout_ms,'solver':z3.get_version_string(),'engine':args.engine,'clauses':len(solver.assertions())}),flush=True)
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
    selected_edge=next(e for c,e in zip(chosen_edges,edges) if z3.is_true(model.eval(c))) if chosen_edges else (0,P)
    print('selected_edge',selected_edge,flush=True)
    vv=[{(1,0)} if i==selected_edge[0] else {(0,1)} if i==selected_edge[1] else set() for i in range(n)]
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
    if args.two_dirty_cone:
        negative_mask = sum(1 << j for j,x in enumerate(assignments) if not graph_value(x))
        below_values=[not (v & negative_mask) for v in tt[n:]]
        ancestors=[]
        top_form=True
        counts_in_cones=[]
        for j,(op,a,b) in enumerate(gates):
            cone=set()
            for w in (a,b):
                if w>=n:
                    cone.add(w-n)
                    cone |= ancestors[w-n]
            ancestors.append(cone)
            if op=='and':
                if any(gates[i][0]=='and' and below_values[i] for i in cone):
                    top_form=False
                if below_values[j]:
                    counts_in_cones.append((j,sum(gates[i][0]=='and' and not below_values[i] for i in cone)))
        print('top_form',top_form,'dirty_counts_in_top_cones',counts_in_cones,flush=True)
        assert top_form and any(k>=2 for j,k in counts_in_cones)
    prefix.with_suffix('.model.json').write_text(json.dumps({'P':P,'L':L,'edges':edges,'gates':gates,'output':n+len(gates)-1,'read_bound':args.read_bound,'reads_at_most_bound':read2},indent=2)+'\n')
elif result==z3.unknown:
    print('reason_unknown',solver.reason_unknown(),flush=True)
