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


from pathlib import Path
import argparse

BASE = Path(__file__).with_name('search_petersen_baseline.json')

def solve_case(label, gate_count, and_count, first_op, first_b, seconds, output_dir, fixed=None):
    data=json.loads(BASE.read_text())
    n=data['input_count']; rows=data['critical_rows']; edges=data['edges']
    width=len(rows); pointer_bits=(n+gate_count-1).bit_length()
    def bv(k,w=pointer_bits): return f'(_ bv{k} {w})'
    def mux(index,values):
        term=values[-1]
        for k in reversed(range(len(values)-1)):
            term=f'(ite (= {index} {bv(k)}) {values[k]} {term})'
        return term
    cfg=mk_config();param(cfg,b'model',b'true');param(cfg,b'timeout',str(seconds*1000).encode())
    ctx=context(cfg);del_config(cfg);solver=solver_new(ctx);solver_inc(ctx,solver)
    commands=['(set-logic QF_BV)']
    wires=[bv(x,width) for x in data['packed_input_signatures']]
    for j in range(gate_count):
        commands += [f'(declare-const a{j} (_ BitVec {pointer_bits}))',f'(declare-const b{j} (_ BitVec {pointer_bits}))',f'(declare-const o{j} Bool)',
                     f'(assert (bvult a{j} {bv(n+j)}))',f'(assert (bvult b{j} {bv(n+j)}))',f'(assert (bvule a{j} b{j}))']
        av=mux(f'a{j}',wires);bv_=mux(f'b{j}',wires)
        commands += [f'(declare-const w{j} (_ BitVec {width}))',f'(assert (= w{j} (ite o{j} (bvor {av} {bv_}) (bvand {av} {bv_}))))']
        wires.append(f'w{j}')
    commands.append(f'(assert (= {wires[-1]} {bv(data["packed_goal"],width)}))')
    if and_count is not None:
        summands=[f'(ite o{j} {bv(0)} {bv(1)})' for j in range(gate_count)]
        commands.append(f'(assert (= (bvadd {" ".join(summands)}) {bv(and_count)}))')
    if first_op is not None:
        commands += [f'(assert (= a0 {bv(0)}))',f'(assert (= b0 {bv(first_b)}))',f'(assert (= o0 {str(bool(first_op)).lower()}))']
    if fixed is None:
        for i in range(gate_count-1):
            readers=[f'(or (= a{j} {bv(n+i)}) (= b{j} {bv(n+i)}))' for j in range(i+1,gate_count)]
            commands.append(f'(assert (or {" ".join(readers)}))')
    else:
        for j,(op,a,b) in enumerate(fixed):
            a,b=sorted([a,b])
            commands += [f'(assert (= a{j} {bv(a)}))',f'(assert (= b{j} {bv(b)}))',f'(assert (= o{j} {str(bool(op)).lower()}))']
    query='\n'.join(commands)+'\n'
    (output_dir/(label+'.smt2')).write_text(query)
    read(ctx,solver,query.encode());start=time.monotonic();status=check(ctx,solver)
    result={'label':label,'gates':gate_count,'and_count':and_count,'first_op':first_op,'first_b':first_b,'status':status,'seconds':time.monotonic()-start,'scope':'finite SMT search only; no Lean lower-bound certificate'}
    if status==0:result['unknown_reason']=unknown(ctx,solver).decode()
    if status==1:
        model=model_get(ctx,solver);model_inc(ctx,model);mt=model_text(ctx,model).decode()
        (output_dir/(label+'.model.txt')).write_text(mt)
        pairs=dict(re.findall(r'([a-z][0-9]+) -> (#[xb][0-9a-f]+|true|false)',mt))
        def val(key):
            atom=pairs[key]
            if atom in ('true','false'):return int(atom=='true')
            return int(atom[2:],16 if atom[1]=='x' else 2)
        gates=[[val('o'+str(j)),val('a'+str(j)),val('b'+str(j))] for j in range(gate_count)]
        fp=[];fn=[]
        for x in range(1<<n):
            values=[bool(x>>i&1) for i in range(n)]
            for op,a,b in gates:values.append((values[a] or values[b]) if op else (values[a] and values[b]))
            target=any((x>>a&1) and (x>>b&1) for a,b in edges)
            if values[-1] and not target:fp.append(x)
            if target and not values[-1]:fn.append(x)
        result.update(gate_list=gates,false_positives=fp,false_negatives=fn,exact=(not fp and not fn))
        assert not fp and not fn,'packed critical-row solution failed full independent simulation'
    print(json.dumps(result),flush=True)
    (output_dir/(label+'.result.json')).write_text(json.dumps(result,indent=2)+'\n')
    del_context(ctx)
    return status

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--seconds',type=int,default=120)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--smoke',action='store_true')
    args=parser.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    data=json.loads(BASE.read_text())
    solve_case('positive20',20,None,None,None,5,args.out,fixed=data['baseline_gates'])
    if not args.smoke:
        for count in [6,7]:
            for op,b,name in [(0,1,'and_edge'),(1,1,'or_edge'),(1,2,'or_nonedge')]:
                status=solve_case(f'andcount{count}_{name}',19,count,op,b,args.seconds,args.out)
                if status==1:sys.exit(0)
