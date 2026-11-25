import argparse
import itertools
import json
import math
import time
import z3
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('graph',choices=['path4','cycle5','cycle6','theta233','petersen','fano','sharedfilter','external'])
parser.add_argument('gates',type=int)
parser.add_argument('--timeout',type=int,default=120)
parser.add_argument('--require-bad-own',action='store_true')
parser.add_argument('--require-singleton-and',action='store_true')
parser.add_argument('--ordered',action='store_true')
parser.add_argument('--distinct-prefix',action='store_true')
parser.add_argument('--pair-orbits',action='store_true')
parser.add_argument('--graph-json')
parser.add_argument('--dimacs')
parser.add_argument('--cadical-output')
args=parser.parse_args()

if args.graph=='path4':
    n=4;edges=[(0,1),(1,2),(2,3)]
elif args.graph=='cycle5':
    n=5;edges=[(i,(i+1)%5) for i in range(5)]
elif args.graph=='cycle6':
    n=6;edges=[(i,(i+1)%6) for i in range(6)]
elif args.graph=='theta233':
    n=7;edges=[(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]
elif args.graph=='petersen':
    n=10;edges=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(i+5,(i+2)%5+5) for i in range(5)]
elif args.graph=='sharedfilter':
    n=8;edges=[(0,1),(2,3),(0,4),(2,4),(1,5),(3,5),(0,6),(3,6),(1,7),(2,7)]
elif args.graph=='fano':
    n=14;lines=[(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]
    edges=[(p,7+j) for j,line in enumerate(lines) for p in line]

if args.graph=='external':
    assert args.graph_json is not None
    with open(args.graph_json) as source: graph_data=json.load(source)
    n=graph_data['n'];edges=graph_data['edges']
edges=sorted({tuple(sorted(e)) for e in edges})
edge_masks=[(1<<a)|(1<<b) for a,b in edges]
neighbors=[0]*n
for a,b in edges:
    neighbors[a]|=1<<b;neighbors[b]|=1<<a
independent=[]
for x in range(1<<n):
    if any(x&e==e for e in edge_masks):continue
    if all(x&(1<<i) or x&neighbors[i] for i in range(n)):
        independent.append(x)
tau=n-max(x.bit_count() for x in independent)
singleton_offset=len(edge_masks)+len(independent)
samples=edge_masks+independent+([1<<i for i in range(n)] if args.require_singleton_and else [])
bits=len(samples)
mask=(1<<bits)-1
base_values=[sum(1<<j for j,x in enumerate(samples) if x&(1<<i)) for i in range(n)]+[0,mask]
target=(1<<len(edges))-1
k=args.gates
idxbits=max(1,(n+k+1).bit_length())
solver=z3.SolverFor('QF_BV')
solver.set(timeout=args.timeout*1000)
values=[z3.BitVecVal(v,bits) for v in base_values]
aa=[];bb=[];oo=[];active=[]

def select(index,signals):
    result=signals[0]
    for i,value in enumerate(signals[1:],1):
        result=z3.If(index==i,value,result)
    return result

start=time.time()
for i in range(k):
    a=z3.BitVec('a'+str(i),idxbits);b=z3.BitVec('b'+str(i),idxbits)
    op=z3.Bool('and'+str(i))
    value=z3.BitVec('v'+str(i),bits)
    solver.add(z3.ULE(a,b),z3.ULT(b,len(values)))
    lhs=select(a,values);rhs=select(b,values)
    solver.add(value==z3.If(op,lhs&rhs,lhs|rhs))
    # Free constants can be removed from a circuit for a nonconstant graph function;
    # padding with copies of its output permits an exact k-gate encoding.
    solver.add(value!=0,value!=mask)
    on=z3.Bool('active'+str(i)) if args.distinct_prefix else z3.BoolVal(True)
    if args.distinct_prefix:
        if i==0: solver.add(on)
        else:
            solver.add(z3.Implies(on,active[i-1]))
            solver.add(z3.Implies(z3.Not(on),z3.And(z3.Not(op),a==n+2+i-1,b==n+2+i-1)))
        solver.add(z3.Implies(on,z3.And([value!=old for old in values])))
    aa.append(a);bb.append(b);oo.append(op);values.append(value);active.append(on)
for i in range(k-1):
    solver.add(z3.Or([z3.Or(aa[j]==n+2+i,bb[j]==n+2+i) for j in range(i+1,k)]))
solver.add(values[-1]==target)
if args.ordered:
    for i in range(k-1):
        solver.add(z3.ULE(bb[i],bb[i+1]))
        solver.add(z3.Implies(bb[i]==bb[i+1],z3.ULE(aa[i],aa[i+1])))
        solver.add(z3.Implies(z3.And(aa[i]==aa[i+1],bb[i]==bb[i+1]),z3.Or(z3.Not(oo[i]),oo[i+1])))
if args.require_singleton_and:
    solver.add(z3.Or([z3.And(oo[j],z3.Or([z3.Extract(singleton_offset+i,singleton_offset+i,values[n+2+j])==1 for i in range(n)])) for j in range(k)]))

if args.pair_orbits:
    degrees=[x.bit_count() for x in neighbors]
    order=[]
    while len(order)<n:
        order.append(max((v for v in range(n) if v not in order),key=lambda v:(sum((neighbors[v]>>u)&1 for u in order),degrees[v],-v)))
    automorphisms=[]
    mapping=[-1]*n
    def find_aut(level,used):
        if level==n:
            automorphisms.append(tuple(mapping));return
        v=order[level]
        for w in range(n):
            if used&(1<<w) or degrees[v]!=degrees[w]:continue
            if any(((neighbors[v]>>u)&1)!=((neighbors[w]>>mapping[u])&1) for u in order[:level]):continue
            mapping[v]=w
            find_aut(level+1,used|(1<<w))
            mapping[v]=-1
    find_aut(0,0)
    pairs=set(itertools.combinations(range(n),2));representatives=[]
    while pairs:
        p=min(pairs)
        orbit={tuple(sorted((a[p[0]],a[p[1]]))) for a in automorphisms}
        representatives.append(min(orbit,key=lambda q:(q[1],q[0])))
        pairs-=orbit
    solver.add(z3.Or([z3.And(aa[0]==a,bb[0]==b) for a,b in representatives]))
    print(json.dumps({'automorphisms':len(automorphisms),'first_pair_representatives':representatives}),flush=True)

if args.require_bad_own:
    # Exact ancestor relation in a topologically ordered circuit.
    cones=[]
    for j in range(k):
        row=[]
        for i in range(j):
            direct=z3.Or(aa[j]==n+2+i,bb[j]==n+2+i)
            indirect=[z3.And(z3.Or(aa[j]==n+2+t,bb[j]==n+2+t),cones[t][i]) for t in range(i+1,j)]
            row.append(z3.Or([direct]+indirect))
        cones.append(row)
    bad=[]
    for j in range(k):
        not_owned=[]
        for e in range(len(edges)):
            earlier=[z3.And(cones[j][i],oo[i],z3.Extract(e,e,values[n+2+i])==1) for i in range(j)]
            not_owned.append(z3.Or(z3.Extract(e,e,values[n+2+j])==0,z3.Or(earlier)))
        bad.append(z3.And([oo[j]]+not_owned))
    solver.add(z3.Or(bad))

print(json.dumps({'graph':args.graph,'n':n,'edges':edges,'tau':tau,'cover_upper':len(edges)+tau-1,'samples':bits,'max_independent_sets':len(independent),'gates':k,'require_bad_own':args.require_bad_own,'require_singleton_and':args.require_singleton_and,'ordered':args.ordered,'distinct_prefix':args.distinct_prefix,'pair_orbits':args.pair_orbits,'build_seconds':time.time()-start}),flush=True)
external_model=None
if args.dimacs or args.cadical_output:
    goal=z3.Goal(models=True)
    goal.add(*solver.assertions())
    transformed=z3.Then('simplify','propagate-values','solve-eqs','bit-blast','tseitin-cnf')(goal)
    assert len(transformed)==1
    cnf_goal=transformed[0]
    cnf=cnf_goal.dimacs()
    if args.cadical_output:
        assert Path(args.dimacs).read_text()==cnf, 'recreated CNF differs from solved file'
        text=Path(args.cadical_output).read_text()
        assert 's SATISFIABLE' in text.splitlines()
        assignment={}
        for line in text.splitlines():
            if line.startswith('v '):
                for raw in line.split()[1:]:
                    value=int(raw)
                    if value:assignment[abs(value)]=value>0
        names={}
        clauses=[]
        for line in cnf.splitlines():
            parts=line.split()
            if len(parts)>=3 and parts[0]=='c' and parts[1].isdigit(): names[int(parts[1])]=parts[2]
            elif parts and parts[0] not in ['c','p']:clauses.append([int(t) for t in parts if t!='0'])
        assert all(any(assignment[abs(l)]==(l>0) for l in c) for c in clauses), 'CNF assignment fails a clause'
        cnf_variables={}
        stack=[cnf_goal.as_expr()];seen=set()
        while stack:
            expression=stack.pop();identity=expression.get_id()
            if identity in seen:continue
            seen.add(identity)
            if z3.is_const(expression) and not z3.is_true(expression) and not z3.is_false(expression):
                cnf_variables[str(expression.decl().name())]=expression
            else:stack.extend(expression.children())
        boolean_model=z3.Model()
        for index,value in assignment.items():boolean_model.update_value(cnf_variables[names[index]],z3.BoolVal(value))
        assert z3.is_true(boolean_model.eval(cnf_goal.as_expr())), 'constructed Boolean model fails CNF goal'
        external_model=cnf_goal.convert_model(boolean_model)
        failed=[a for a in solver.assertions() if not z3.is_true(external_model.eval(a,model_completion=True))]
        if failed:
            Path(args.cadical_output+'.reconstruction-debug').write_text(external_model.sexpr()+'\n\nFAILED\n'+'\n'.join(str(a) for a in failed))
            print('Failed assertions:',[str(a) for a in failed[:5]],flush=True)
        assert not failed, 'converted model fails original encoding'
    else:
        Path(args.dimacs).write_text(cnf)
        print(json.dumps({'dimacs':args.dimacs,'bytes':len(cnf),'export_seconds':time.time()-start}),flush=True)
        raise SystemExit(0)
result=z3.sat if external_model is not None else solver.check()
report={'result':str(result),'seconds':time.time()-start,'reason_unknown':solver.reason_unknown() if result==z3.unknown else None}
if result==z3.sat:
    model=external_model if external_model is not None else solver.model()
    gates=[]
    semantic=[sum(1<<x for x in range(1<<n) if x&(1<<i)) for i in range(n)]+[0,(1<<(1<<n))-1]
    cone_list=[set() for _ in semantic]
    for j in range(k):
        a=model.eval(aa[j]).as_long();b=model.eval(bb[j]).as_long();op=z3.is_true(model.eval(oo[j]))
        value=(semantic[a]&semantic[b]) if op else (semantic[a]|semantic[b])
        cone=cone_list[a]|cone_list[b]
        for operand in [a,b]:
            if operand>=n+2 and gates[operand-n-2]['op']=='and':cone.add(operand-n-2)
        owned=[]
        if op:
            for (u,v),x in zip(edges,edge_masks):
                if (value>>x)&1 and all(not ((semantic[n+2+i]>>x)&1) for i in cone):owned.append([u,v])
        gates.append({'active':z3.is_true(model.eval(active[j])),'op':'and' if op else 'or','a':a,'b':b,'owned':owned,'singleton_true':[i for i in range(n) if (value>>(1<<i))&1]})
        semantic.append(value);cone_list.append(cone)
    exact_target=sum(1<<x for x in range(1<<n) if any(x&e==e for e in edge_masks))
    report.update(gates=gates,exact_function_verified=semantic[-1]==exact_target,all_ands_own=all(g['owned'] for g in gates if g['op']=='and'))
print(json.dumps(report,indent=2),flush=True)
