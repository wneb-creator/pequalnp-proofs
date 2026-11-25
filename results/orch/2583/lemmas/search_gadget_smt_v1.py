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

import json
import re
import sys

def solve(name,n,gates,edges,bad_edge,seconds):
    def target(x):return any(x>>a&1 and x>>b&1 for a,b in edges)
    false=[x for x in range(1<<n) if not target(x)]
    maximal=[x for x in false if all(target(x|(1<<i)) for i in range(n) if not(x>>i&1))]
    rows=maximal+sorted({(1<<a)|(1<<b) for a,b in edges})
    width=len(rows);bits=(n+gates-1).bit_length()
    def bv(k,w=bits):return f'(_ bv{k} {w})'
    cfg=mk_config();param(cfg,b'model',b'true');param(cfg,b'timeout',str(seconds*1000).encode())
    ctx=context(cfg);del_config(cfg);solver=solver_new(ctx);solver_inc(ctx,solver)
    cmds=['(set-logic QF_BV)']
    wires=[bv(sum(((x>>i)&1)<<j for j,x in enumerate(rows)),width) for i in range(n)]
    linear=[bv(1<<i,n) for i in range(n)]
    readone=['false']*n
    p,q=bad_edge if bad_edge is not None else (0,0)
    def bit(v,k):return f'(= ((_ extract {k} {k}) {v}) #b1)'
    def mux(v,values):
        result=values[-1]
        for k in reversed(range(len(values)-1)):result=f'(ite (= {v} {bv(k)}) {values[k]} {result})'
        return result
    for j in range(gates):
        cmds.extend([f'(declare-const a{j} (_ BitVec {bits}))',f'(declare-const b{j} (_ BitVec {bits}))',f'(declare-const o{j} Bool)',
                     f'(assert (bvult a{j} {bv(n+j)}))',f'(assert (bvult b{j} {bv(n+j)}))',f'(assert (bvule a{j} b{j}))'])
        av,bval=mux(f'a{j}',wires),mux(f'b{j}',wires)
        wn=f'w{j}'
        cmds.extend([f'(declare-const {wn} (_ BitVec {width}))',f'(assert (= {wn} (ite o{j} (bvor {av} {bval}) (bvand {av} {bval}))))'])
        if bad_edge is not None:
            al,bl=mux(f'a{j}',linear),mux(f'b{j}',linear)
            ar,br=mux(f'a{j}',readone),mux(f'b{j}',readone)
            ln,rn=f'l{j}',f'r{j}'
            pair=f'(or (and {bit(al,p)} {bit(bl,q)}) (and {bit(al,q)} {bit(bl,p)}))'
            cmds.extend([f'(declare-const {ln} (_ BitVec {n}))',f'(assert (= {ln} (ite o{j} (bvor {al} {bl}) {bv(0,n)})))',
                         f'(declare-const {rn} Bool)',f'(assert (= {rn} (ite o{j} (or {ar} {br}) {pair})))'])
            linear.append(ln);readone.append(rn)
        wires.append(wn)
    goal=sum(int(target(x))<<j for j,x in enumerate(rows))
    cmds.append(f'(assert (= {wires[-1]} {bv(goal,width)}))')
    if bad_edge is not None:cmds.append(f'(assert (not {readone[-1]}))')
    for i in range(gates-1):
        cmds.append('(assert (or '+' '.join(f'(or (= a{j} {bv(n+i)}) (= b{j} {bv(n+i)}))' for j in range(i+1,gates))+'))')
    read(ctx,solver,'\n'.join(cmds).encode())
    start=time.monotonic();status=check(ctx,solver)
    print(json.dumps({'name':name,'n':n,'gates':gates,'critical_rows':width,'edges':edges,'bad_edge':bad_edge,'status':status,'seconds':time.monotonic()-start}),flush=True)
    if status==0:print('reason',unknown(ctx,solver).decode(),flush=True)
    if status==1:
        model=model_get(ctx,solver);model_inc(ctx,model);mt=model_text(ctx,model).decode();print(mt,flush=True)
    del_context(ctx)

if __name__=='__main__':
    seconds=int(sys.argv[1]) if len(sys.argv)>1 else 10
    two=[(0,5),(1,5),(2,5),(0,6),(3,6),(4,6)]
    three=[(0,6),(2,6),(3,6),(0,7),(1,7),(4,7),(1,8),(2,8),(5,8)]
    k4=[]
    for k,(i,j) in enumerate(( (i,j) for i in range(4) for j in range(i+1,4) )):k4.extend([(i,4+k),(j,4+k)])
    solve('two-stars-shared',7,7,two,(0,5),seconds)
    solve('two-stars-private',7,7,two,(1,5),seconds)
    solve('three-stars-intersection',9,11,three,(0,6),seconds)
    solve('three-stars-private',9,11,three,(3,6),seconds)
    solve('K4-incidence-subdivision',10,14,k4,None,seconds)
