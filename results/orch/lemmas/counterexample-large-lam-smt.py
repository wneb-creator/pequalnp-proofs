"""Exact finite largeLam residual search; solver UNKNOWN proves nothing.

The graph is an unknown nonempty C4-free subgraph of K_3,3. Every one of
64 assignments is encoded. TopForm, T=0, and all gates in the output cone
are imposed. A near bound limits size to |E|+tau(E)-1+near. No claim that
these circuits are size-minimal is made. Sum or separate residual failures
can be requested. Pure conjunction buffers and repeated input wires remain
allowed. Native Z3 is used through its installed public C interface.
"""
import argparse
import ctypes
import json
from pathlib import Path
import time


def problem(gates=8, timeout=300000, near=2, violation='sum', pin=False):
    n, p, bits = 6, 3, 64
    iw = (n + gates).bit_length()
    count_width = (2 * gates + 10).bit_length()
    ts = ['(set-option :produce-models true)', f'(set-option :timeout {timeout})',
          '(set-option :memory_max_size 2000)', '(set-logic QF_BV)']
    def bv(x, w): return f'(_ bv{x} {w})'
    def land(xs):
        xs = list(xs)
        return '(and ' + ' '.join(xs) + ')' if xs else 'true'
    def lor(xs):
        xs = list(xs)
        return '(or ' + ' '.join(xs) + ')' if xs else 'false'
    def bvor(xs, w):
        xs = list(xs)
        if not xs: return bv(0, w)
        out = xs[0]
        for x in xs[1:]: out = f'(bvor {out} {x})'
        return out
    def cnt(xs):
        out = bv(0, count_width)
        for x in xs: out = f'(bvadd {out} (ite {x} {bv(1,count_width)} {bv(0,count_width)}))'
        return out
    def decl(s,w): ts.append(f'(declare-const {s} {w})')
    def define(s,w,value): ts.append(f'(define-fun {s} () {w} {value})')
    def define_count(s,xs): define(s,f'(_ BitVec {count_width})',cnt(xs))
    def assert_(s): ts.append('(assert ' + s + ')')
    def nonzero(s,w): return f'(distinct {s} {bv(0,w)})'
    def has(s,i,w): return nonzero(f'(bvand {s} {bv(1<<i,w)})',w)
    def mux(s,prefix,end):
        out=f'{prefix}{end-1}'
        for k in reversed(range(end-1)):out=f'(ite (= {s} {bv(k,iw)}) {prefix}{k} {out})'
        return out
    edges=[(a,3+b) for a in range(3) for b in range(3)]
    for e in range(9): decl(f'e{e}','Bool')
    assert_(lor(f'e{e}' for e in range(9)))
    for a in range(3):
        for aa in range(a+1,3):
            for b in range(3):
                for bb in range(b+1,3):
                    assert_(f'(not {land(f"e{u*3+v}" for u in (a,aa) for v in (b,bb))})')
    edge_tables=[sum(1<<x for x in range(64) if x>>a&1 and x>>b&1) for a,b in edges]
    define('goal','(_ BitVec 64)',bvor((f'(ite e{e} {bv(t,64)} {bv(0,64)})' for e,t in enumerate(edge_tables)),64))
    for i in range(n):
        define(f'v{i}','(_ BitVec 64)',bv(sum(1<<x for x in range(64) if x>>i&1),64))
        define(f'r{i}','(_ BitVec 6)',bv(1<<i,6))
        define(f'h{i}',f'(_ BitVec {gates})',bv(0,gates))
        define(f'z{i}',f'(_ BitVec {gates})',bv(0,gates))
    for j in range(gates):
        decl(f'a{j}',f'(_ BitVec {iw})');decl(f'b{j}',f'(_ BitVec {iw})');decl(f'o{j}','Bool')
    for j in range(gates):
        w=n+j
        assert_(f'(bvult a{j} {bv(w,iw)})');assert_(f'(bvult b{j} {bv(w,iw)})');assert_(f'(bvule a{j} b{j})')
        for side in 'ab':
            for prefix,width in [('v',64),('r',6),('h',gates),('z',gates)]:
                define(f'{side}{j}{prefix}',f'(_ BitVec {width})',mux(f'{side}{j}',prefix,w))
        define(f'v{w}','(_ BitVec 64)',f'(ite o{j} (bvor a{j}v b{j}v) (bvand a{j}v b{j}v))')
        define(f'r{w}','(_ BitVec 6)',f'(ite o{j} (bvor a{j}r b{j}r) {bv(0,6)})')
        define(f'h{w}',f'(_ BitVec {gates})',bvor([f'a{j}h',f'b{j}h',bv(1<<j,gates)],gates))
        define(f'z{w}',f'(_ BitVec {gates})',f'(ite o{j} {bvor([f"a{j}z",f"b{j}z",bv(1<<j,gates)],gates)} {bv(1<<j,gates)})')
        assert_(f'(or (= (bvand r{w} {bv(7,6)}) {bv(0,6)}) (= (bvand r{w} {bv(56,6)}) {bv(0,6)}))')
        define(f'clean{j}','Bool',f'(= (bvand v{w} (bvnot goal)) {bv(0,64)})')
        define(f'top{j}','Bool',f'(and (not o{j}) clean{j})')
        define(f'c{j}','Bool',f'(and top{j} (or (= a{j}r {bv(0,6)}) (= b{j}r {bv(0,6)})))')
        define(f'junk{j}','Bool',f'(and (not o{j}) (not clean{j}))')
        define(f'orn{j}','Bool',f'(and o{j} (not clean{j}))')
        for k in range(j): assert_(f'(=> (and top{k} (not o{j})) (not {has(f"h{w}",k,gates)}))')
    assert_(f'(= v{n+gates-1} goal)')
    assert_(f'(= h{n+gates-1} {bv((1<<gates)-1,gates)})')
    def singleton(s):return lor(f'(= {s} {bv(1<<i,6)})' for i in range(6))
    for j in range(gates):
        witnesses=[]
        for k in range(j+1,gates):
            witnesses += [land([f'top{k}',singleton(f'b{k}r'),has(f'a{k}z',j,gates)]),land([f'top{k}',singleton(f'a{k}r'),has(f'b{k}z',j,gates)])]
        define(f'lam{j}','Bool',land([f'orn{j}',nonzero(f'a{j}r',6),nonzero(f'b{j}r',6),lor(witnesses)]))
        define(f'large{j}','Bool',land([f'lam{j}',nonzero(f'r{n+j}',6),f'(not {singleton(f"r{n+j}")})']))
    for e,(a,b) in enumerate(edges):
        represented=[]
        for j in range(gates):
            represented.append(land([f'top{j}',lor([land([has(f'a{j}r',a,6),has(f'b{j}r',b,6)]),land([has(f'a{j}r',b,6),has(f'b{j}r',a,6)])])]))
        define(f'u{e}','Bool',land([f'e{e}',f'(not {lor(represented)})']))
    def tau(prefix,label):
        # tau is the number of k=0,1,2 for which no k-element vertex cover exists;
        # every bipartite graph on 3+3 vertices has a cover of size at most 3.
        tests=[]
        for k in range(3):
            covers=[]
            for mask in range(64):
                if mask.bit_count()!=k:continue
                covers.append(land(f'(not {prefix}{e})' for e,(a,b) in enumerate(edges) if not(mask>>a&1 or mask>>b&1)))
            tests.append(f'(not {lor(covers)})')
        define_count(label,tests)
    tau('e','tauE');tau('u','tauU')
    define_count('edges',[f'e{e}' for e in range(9)])
    define_count('uCount',[f'u{e}' for e in range(9)])
    define_count('cCount',[f'c{j}' for j in range(gates)])
    define_count('jCount',[f'junk{j}' for j in range(gates)])
    define_count('oCount',[f'(and orn{j} (not large{j}))' for j in range(gates)])
    define('lhs',f'(_ BitVec {count_width})','(bvadd uCount tauU)')
    define('rhs',f'(_ BitVec {count_width})','(bvadd (bvadd cCount cCount) (bvadd jCount oCount))')
    assert_(f'(bvule {bv(gates+1,count_width)} (bvadd (bvadd edges tauE) {bv(near,count_width)}))')
    if violation=='sum':assert_('(bvugt lhs rhs)')
    elif violation=='and':assert_('(bvugt tauU (bvadd cCount jCount))')
    elif violation=='or':assert_('(bvugt uCount (bvadd cCount oCount))')
    if pin:
        known=[('or',0,1),('or',3,4),('and',6,7),('or',2,8),('and',9,3),('or',5,8),('and',11,0),('or',10,12)]
        assert gates==8
        for j,(op,a,b) in enumerate(known):
            a,b=sorted((a,b))
            assert_(f'(= a{j} {bv(a,iw)})');assert_(f'(= b{j} {bv(b,iw)})');assert_(f'(= o{j} {str(op=="or").lower()})')
    ts.append('(check-sat)')
    symbols=[f'{s}{j}' for j in range(gates) for s in 'abo']+[f'e{e}' for e in range(9)]+['edges','tauE','uCount','tauU','cCount','jCount','oCount','lhs','rhs']
    return '\n'.join(ts),' '.join(symbols)


def run(source,symbols):
    z=ctypes.CDLL('/usr/lib/x86_64-linux-gnu/libz3.so.4')
    z.Z3_mk_config.restype=ctypes.c_void_p
    z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p
    z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
    z.Z3_del_context.argtypes=[ctypes.c_void_p];z.Z3_del_config.argtypes=[ctypes.c_void_p]
    cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);start=time.monotonic()
    answer=z.Z3_eval_smtlib2_string(ctx,source.encode()).decode();print(answer,flush=True)
    print('elapsed_seconds',time.monotonic()-start,flush=True)
    if answer.strip()=='sat': print(z.Z3_eval_smtlib2_string(ctx,('(get-value ('+symbols+'))').encode()).decode(),flush=True)
    z.Z3_del_context(ctx);z.Z3_del_config(cfg)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gates',type=int,default=8);parser.add_argument('--timeout',type=int,default=300000)
    parser.add_argument('--near',type=int,default=2);parser.add_argument('--violation',choices=['sum','and','or','none'],default='sum')
    parser.add_argument('--pin',action='store_true');parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();source,symbols=problem(args.gates,args.timeout,args.near,args.violation,args.pin)
    args.output.write_text(source+'\n');print(json.dumps(vars(args),default=str),flush=True);print('smt_bytes',len(source),flush=True)
    run(source,symbols)
