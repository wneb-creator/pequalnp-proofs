import ctypes as C
import ctypes.util
import json
import random
import re
import sys
import time
from pathlib import Path

Z = C.CDLL(ctypes.util.find_library('z3'))
P = C.c_void_p
S = C.c_char_p
I = C.c_int
def bind(name, ret, *args):
    fn = getattr(Z, name)
    fn.restype = ret
    fn.argtypes = list(args)
    return fn
mk_config = bind('Z3_mk_config', P)
set_param = bind('Z3_set_param_value', None, P, S, S)
mk_context = bind('Z3_mk_context', P, P)
del_config = bind('Z3_del_config', None, P)
del_context = bind('Z3_del_context', None, P)
mk_solver = bind('Z3_mk_solver', P, P)
inc_solver = bind('Z3_solver_inc_ref', None, P, P)
solver_read = bind('Z3_solver_from_string', None, P, P, S)
solver_check = bind('Z3_solver_check', I, P, P)
solver_model = bind('Z3_solver_get_model', P, P, P)
inc_model = bind('Z3_model_inc_ref', None, P, P)
model_text = bind('Z3_model_to_string', S, P, P)
reason_unknown = bind('Z3_solver_get_reason_unknown', S, P, P)

EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x):
    return any(x >> a & 1 and x >> b & 1 for a,b in EDGES)

def evaluate(circ, x):
    wires = [bool(x >> a & 1) for a in range(10)]
    for op, a, b in circ:
        wires.append(wires[a] and wires[b] if op == 0 else wires[a] or wires[b] if op == 1 else not wires[a])
    return wires[-1]

def bv(n, width):
    return f'(_ bv{n} {width})'

def synthesize(seconds, first, fixed=None, not_count=None):
    fixed = fixed or {}
    config=mk_config()
    set_param(config,b'model',b'true')
    set_param(config,b'timeout',str(int(seconds*1000)).encode())
    ctx=mk_context(config)
    del_config(config)
    solver=mk_solver(ctx)
    inc_solver(ctx,solver)
    commands=['(set-logic QF_BV)']
    for j in range(19):
        for v, width in [('a',5),('b',5),('o',2)]:
            commands.append(f'(declare-const {v}{j} (_ BitVec {width}))')
        commands.extend([
            f'(assert (bvult a{j} {bv(10+j,5)}))',
            f'(assert (bvult b{j} {bv(10+j,5)}))',
            f'(assert (bvule o{j} {bv(2,2)}))',
            f'(assert (or (= o{j} {bv(2,2)}) (bvule a{j} b{j})))',
            f'(assert (or (not (= o{j} {bv(2,2)})) (= a{j} b{j})))',
        ])
    for i in range(18):
        commands.append('(assert (or '+' '.join(
            f'(or (= a{j} {bv(10+i,5)}) (and (not (= o{j} {bv(2,2)})) (= b{j} {bv(10+i,5)})))'
            for j in range(i+1,19))+'))')
    commands.append('(assert (or '+' '.join(f'(= o{j} {bv(2,2)})' for j in range(19))+'))')
    nots='(bvadd '+' '.join(f'(ite (= o{j} {bv(2,2)}) {bv(1,5)} {bv(0,5)})' for j in range(19))+')'
    commands.append(f'(assert (bvule {nots} {bv(3,5)}))')
    if not_count is not None:
        commands.append(f'(assert (= {nots} {bv(not_count,5)}))')
    if first is not None:
        fixed[0]=first
        op,a,b=first
        if op!=2 and a!=b:
            for v in [a,b]:
                commands.append('(assert (or '+' '.join(
                    f'(or (= a{j} {bv(v,5)}) (= b{j} {bv(v,5)}))' for j in range(1,19))+'))')
    for j,(op,a,b) in fixed.items():
        if op!=2 and a>b:a,b=b,a
        if op==2:b=a
        commands.extend([f'(assert (= o{j} {bv(op,2)}))',f'(assert (= a{j} {bv(a,5)}))',f'(assert (= b{j} {bv(b,5)}))'])
    solver_read(ctx,solver,'\n'.join(commands).encode())
    samples = [x for x in range(1024) if not target(x)] + [(1<<a)|(1<<b) for a,b in EDGES]
    rounds=0
    start=time.monotonic()
    while time.monotonic()-start < seconds:
        batch=samples
        width=len(batch)
        commands=[]
        wires=[bv(sum(((x>>a)&1)<<i for i,x in enumerate(batch)),width) for a in range(10)]
        for j in range(19):
            def mux(var):
                out=wires[-1]
                for k in reversed(range(len(wires)-1)):
                    out=f'(ite (= {var} {bv(k,5)}) {wires[k]} {out})'
                return out
            left=mux(f'a{j}')
            right=mux(f'b{j}')
            commands.append(f'(declare-const w{rounds}_{j} (_ BitVec {width}))')
            commands.append(f'(assert (= w{rounds}_{j} (ite (= o{j} {bv(0,2)}) (bvand {left} {right}) (ite (= o{j} {bv(1,2)}) (bvor {left} {right}) (bvnot {left})))))')
            wires.append(f'w{rounds}_{j}')
        commands.append(f'(assert (= {wires[-1]} {bv(sum(int(target(x))<<i for i,x in enumerate(batch)),width)}))')
        solver_read(ctx,solver,'\n'.join(commands).encode())
        status=solver_check(ctx,solver)
        print('status',status,'elapsed',round(time.monotonic()-start,3),'round',rounds,'samples',len(batch),flush=True)
        if status!=1:
            if status==0:print('unknown',reason_unknown(ctx,solver).decode(),flush=True)
            del_context(ctx)
            return None
        model=solver_model(ctx,solver)
        inc_model(ctx,model)
        text=model_text(ctx,model).decode()
        values={}
        for name,number in re.findall(r'\b([abo]\d+) -> (#b[01]+|#x[0-9a-f]+)',text):
            values[name]=int(number[2:],2 if number.startswith('#b') else 16)
        if len(values)!=57:
            print('MODEL_PARSE_FAILURE',text,flush=True)
            del_context(ctx)
            return None
        circ=[(values[f'o{j}'],values[f'a{j}'],values[f'b{j}']) for j in range(19)]
        failures=[x for x in range(1024) if evaluate(circ,x)!=target(x)]
        print('candidate',json.dumps(circ),'failures',len(failures),flush=True)
        if not failures:
            print('FOUND',json.dumps(circ),flush=True)
            del_context(ctx)
            return circ
        samples=failures
        rounds+=1
    del_context(ctx)
    return None

if __name__=='__main__':
    seconds=float(sys.argv[1]) if len(sys.argv)>1 else 60
    case=int(sys.argv[2]) if len(sys.argv)>2 else 0
    not_count=int(sys.argv[3]) if len(sys.argv)>3 else None
    first=[(2,0,0),(0,0,1),(0,0,2),(1,0,1),(1,0,2)][case]
    synthesize(seconds,first,not_count=not_count)
