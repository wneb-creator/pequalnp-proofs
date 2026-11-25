import importlib.util
import json
import re
import sys
import time

spec=importlib.util.spec_from_file_location('search_smt','results/orch/lemmas/search_smt.py')
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

m.EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def evaluate_residual(circ,x):
    wires=[bool(x>>a&1) for a in range(9)]
    for op,a,b in circ:
        wires.append(wires[a] and wires[b] if op==0 else wires[a] or wires[b] if op==1 else not wires[a])
    return wires[-1]
m.evaluate=evaluate_residual

def synthesize(seconds, case, not_count=1):
    first=[(2,0,0),(0,0,1),(0,4,6),(1,0,1),(1,4,6)][case]
    config=m.mk_config()
    m.set_param(config,b'model',b'true')
    m.set_param(config,b'timeout',str(int(seconds*1000)).encode())
    ctx=m.mk_context(config)
    m.del_config(config)
    solver=m.mk_solver(ctx)
    m.inc_solver(ctx,solver)
    commands=['(set-logic QF_BV)']
    def exact_one(names):
        commands.append('(assert (or '+' '.join(names)+'))')
        for i,a in enumerate(names):
            for b in names[:i]:commands.append(f'(assert (or (not {a}) (not {b})))')
    for j in range(16):
        for tag in ['A','B']:
            names=[f'{tag}{j}_{i}' for i in range(9+j)]
            commands.extend(f'(declare-const {v} Bool)' for v in names)
            exact_one(names)
        names=[f'O{j}_{i}' for i in range(3)]
        commands.extend(f'(declare-const {v} Bool)' for v in names)
        exact_one(names)
        for i in range(9+j):
            commands.append(f'(assert (or (not O{j}_2) (= A{j}_{i} B{j}_{i})))')
            for k in range(i):
                commands.append(f'(assert (or O{j}_2 (not A{j}_{i}) (not B{j}_{k})))')
    for i in range(15):
        uses=[f'(or A{j}_{9+i} (and (not O{j}_2) B{j}_{9+i}))' for j in range(i+1,16)]
        commands.append('(assert (or '+' '.join(uses)+'))')
    nots='(bvadd '+' '.join(f'(ite O{j}_2 {m.bv(1,5)} {m.bv(0,5)})' for j in range(16))+')'
    commands.append(f'(assert (= {nots} {m.bv(not_count,5)}))')
    op,a,b=first
    commands.extend([f'(assert O0_{op})',f'(assert A0_{a})',f'(assert B0_{b})'])
    if op!=2:
        for v in [a,b]:
            commands.append('(assert (or '+' '.join(f'(or A{j}_{v} B{j}_{v})' for j in range(1,16))+'))')
    m.solver_read(ctx,solver,'\n'.join(commands).encode())
    samples=[x for x in range(512) if not m.target(x)]+[(1<<a)|(1<<b) for a,b in m.EDGES]
    rounds=0
    start=time.monotonic()
    while time.monotonic()-start < seconds:
        width=len(samples)
        commands=[]
        wires=[m.bv(sum(((x>>a)&1)<<i for i,x in enumerate(samples)),width) for a in range(9)]
        for j in range(16):
            def mux(tag):
                return '(bvor '+' '.join(f'(ite {tag}{j}_{i} {v} {m.bv(0,width)})' for i,v in enumerate(wires))+')'
            left,right=mux('A'),mux('B')
            name=f'w{rounds}_{j}'
            commands.append(f'(declare-const {name} (_ BitVec {width}))')
            commands.append(f'(assert (= {name} (ite O{j}_0 (bvand {left} {right}) (ite O{j}_1 (bvor {left} {right}) (bvnot {left})))))')
            wires.append(name)
        commands.append(f'(assert (= {wires[-1]} {m.bv(sum(int(m.target(x))<<i for i,x in enumerate(samples)),width)}))')
        m.solver_read(ctx,solver,'\n'.join(commands).encode())
        status=m.solver_check(ctx,solver)
        print('status',status,'elapsed',round(time.monotonic()-start,3),'round',rounds,'samples',len(samples),flush=True)
        if status!=1:
            if status==0:print('unknown',m.reason_unknown(ctx,solver).decode(),flush=True)
            m.del_context(ctx)
            return None
        model=m.solver_model(ctx,solver)
        m.inc_model(ctx,model)
        text=m.model_text(ctx,model).decode()
        chosen={}
        for tag,j,i in re.findall(r'\b([ABO])(\d+)_(\d+) -> true\b',text):
            chosen[tag+str(j)]=int(i)
        assert len(chosen)==48, text
        circ=[(chosen[f'O{j}'],chosen[f'A{j}'],chosen[f'B{j}']) for j in range(16)]
        samples=[x for x in range(512) if m.evaluate(circ,x)!=m.target(x)]
        print('candidate',json.dumps(circ),'failures',len(samples),flush=True)
        if not samples:
            print('FOUND',json.dumps(circ),flush=True)
            m.del_context(ctx)
            return circ
        rounds+=1
    m.del_context(ctx)
    return None

if __name__=='__main__':
    synthesize(float(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]) if len(sys.argv)>3 else 1)
