import ctypes as C
import ctypes.util
import time

Z=C.CDLL(ctypes.util.find_library('z3'))
P=C.c_void_p
S=C.c_char_p
def bind(name,ret,*args):
    f=getattr(Z,name);f.restype=ret;f.argtypes=list(args);return f
mk_config=bind('Z3_mk_config',P)
param=bind('Z3_set_param_value',None,P,S,S)
context=bind('Z3_mk_context',P,P)
del_config=bind('Z3_del_config',None,P)
del_context=bind('Z3_del_context',None,P)
solver_new=bind('Z3_mk_solver',P,P)
solver_inc=bind('Z3_solver_inc_ref',None,P,P)
read=bind('Z3_solver_from_string',None,P,P,S)
check=bind('Z3_solver_check',C.c_int,P,P)
model_get=bind('Z3_solver_get_model',P,P,P)
model_inc=bind('Z3_model_inc_ref',None,P,P)
model_text=bind('Z3_model_to_string',S,P,P)
unknown=bind('Z3_solver_get_reason_unknown',S,P,P)

def solve(n,gates,seconds):
    edges=[(i,(i+1)%n) for i in range(n)]
    def target(x):return any(x>>a&1 and x>>b&1 for a,b in edges)
    false=[x for x in range(1<<n) if not target(x)]
    maximal=[x for x in false if all(target(x|(1<<i)) for i in range(n) if not(x>>i&1))]
    rows=maximal+[(1<<a)|(1<<b) for a,b in edges]
    width=len(rows);bits=(n+gates-1).bit_length()
    def bv(k,w=bits):return f'(_ bv{k} {w})'
    cfg=mk_config();param(cfg,b'model',b'true');param(cfg,b'timeout',str(seconds*1000).encode())
    ctx=context(cfg);del_config(cfg);solver=solver_new(ctx);solver_inc(ctx,solver)
    cmds=['(set-logic QF_BV)']
    wires=[bv(sum(((x>>i)&1)<<j for j,x in enumerate(rows)),width) for i in range(n)]
    for j in range(gates):
        cmds.extend([f'(declare-const a{j} (_ BitVec {bits}))',f'(declare-const b{j} (_ BitVec {bits}))',f'(declare-const o{j} Bool)',
                     f'(assert (bvult a{j} {bv(n+j)}))',f'(assert (bvult b{j} {bv(n+j)}))',f'(assert (bvule a{j} b{j}))'])
        def mux(v):
            result=wires[-1]
            for k in reversed(range(len(wires)-1)):result=f'(ite (= {v} {bv(k)}) {wires[k]} {result})'
            return result
        a,b=mux(f'a{j}'),mux(f'b{j}')
        name=f'w{j}'
        cmds.extend([f'(declare-const {name} (_ BitVec {width}))',f'(assert (= {name} (ite o{j} (bvor {a} {b}) (bvand {a} {b}))))'])
        wires.append(name)
    goal=sum(int(target(x))<<j for j,x in enumerate(rows))
    cmds.append(f'(assert (= {wires[-1]} {bv(goal,width)}))')
    cmds.extend([f'(assert (= a0 {bv(0)}))',f'(assert (bvugt b0 {bv(0)}))',f'(assert (bvule b0 {bv(n//2)}))'])
    for i in range(gates-1):
        cmds.append('(assert (or '+' '.join(f'(or (= a{j} {bv(n+i)}) (= b{j} {bv(n+i)}))' for j in range(i+1,gates))+'))')
    read(ctx,solver,'\n'.join(cmds).encode())
    start=time.monotonic();status=check(ctx,solver)
    print('cycle',n,'gates',gates,'critical_rows',width,'status',status,'seconds',time.monotonic()-start,flush=True)
    if status==0:print('reason',unknown(ctx,solver).decode(),flush=True)
    if status==1:
        model=model_get(ctx,solver);model_inc(ctx,model);print(model_text(ctx,model).decode(),flush=True)
    del_context(ctx)

if __name__=='__main__':
    solve(6,7,5)
    solve(8,10,5)
