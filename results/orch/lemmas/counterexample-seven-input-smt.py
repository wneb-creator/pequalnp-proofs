"""Any bounded-size T0 circuit for a specified graph on3+4 inputs.

No dirty-AND, TopForm, minimum, edge-activity, or pivotality condition is used.
A smaller circuit can be trimmed to its output cone and padded to exactly the
requested size with output AND(output, output). Unused gates and idempotent ORs
can therefore be excluded without losing any at-most-size solution. Depth and
lexicographic layer ordering only renumber gates in a topological order.
"""
from pathlib import Path
import ctypes
import sys
import time


def problem(gate_count=7, timeout=300000, pinned=False, edge_mask=303):
    p = 3
    n = 7
    edges = [(a, 3+b) for a in range(3) for b in range(4) if edge_mask>>(4*a+b)&1]
    cases = list(range(128))
    target = sum(1 << s for s in cases if any(s >> a & 1 and s >> b & 1 for a, b in edges))
    bits = len(cases)
    width = (n + gate_count).bit_length()

    def bv(value, bits=width):
        return f'(_ bv{value} {bits})'

    def mux(selector, prefix, count):
        term = f'{prefix}{count - 1}'
        for k in reversed(range(count - 1)):
            term = f'(ite (= {selector} {bv(k)}) {prefix}{k} {term})'
        return term

    text = ['(set-option :produce-models true)', f'(set-option :timeout {timeout})',
            '(set-option :memory_max_size 1000)', '(set-logic QF_BV)']
    for i in range(n):
        value = sum(1 << k for k, s in enumerate(cases) if s >> i & 1)
        text += [f'(define-fun v{i} () (_ BitVec {bits}) {bv(value, bits)})',
                 f'(define-fun c{i} () (_ BitVec 2) {bv(1 if i < p else 2, 2)})',
                 f'(define-fun q{i} () (_ BitVec {width}) {bv(0)})']
    for j in range(gate_count):
        text += [f'(declare-const a{j} (_ BitVec {width}))',
                 f'(declare-const b{j} (_ BitVec {width}))',
                 f'(declare-const o{j} Bool)',
                 f'(declare-const v{n+j} (_ BitVec {bits}))',
                 f'(declare-const c{n+j} (_ BitVec 2))',
                 f'(declare-const q{n+j} (_ BitVec {width}))']
    for j in range(gate_count):
        w = n + j
        text += [f'(assert (bvult a{j} {bv(w)}))', f'(assert (bvult b{j} {bv(w)}))',
                 f'(assert (bvule a{j} b{j}))',
                 f'(assert (=> o{j} (distinct a{j} b{j})))']
        for selector in [f'a{j}', f'b{j}']:
            text += [f'(define-fun {selector}v () (_ BitVec {bits}) {mux(selector, "v", w)})',
                     f'(define-fun {selector}c () (_ BitVec 2) {mux(selector, "c", w)})',
                     f'(define-fun {selector}q () (_ BitVec {width}) {mux(selector, "q", w)})']
        text += [f'(assert (= v{w} (ite o{j} (bvor a{j}v b{j}v) (bvand a{j}v b{j}v))))',
                 f'(assert (= c{w} (ite o{j} (bvor a{j}c b{j}c) {bv(0, 2)})))',
                 f'(assert (distinct c{w} {bv(3, 2)}))',
                 f'(assert (= q{w} (bvadd {bv(1)} (ite (bvule a{j}q b{j}q) b{j}q a{j}q))))']
        if j + 1 < gate_count:
            text.append(f'(assert (bvule q{w} q{w+1}))')
            order = f'(or (and (not o{j}) o{j+1}) (and (= o{j} o{j+1}) (or (bvult a{j} a{j+1}) (and (= a{j} a{j+1}) (bvule b{j} b{j+1})))))'
            text.append(f'(assert (=> (= q{w} q{w+1}) {order}))')
            uses = ' '.join(f'(= {selector}{k} {bv(w)})'
                            for k in range(j + 1, gate_count) for selector in ['a', 'b'])
            text.append(f'(assert (or {uses}))')
    if pinned:
        known = canonical_star_circuit(edges)
        assert gate_count == len(known)
        for j,(op,a,b) in enumerate(known):
            a,b=sorted((a,b))
            text += [f'(assert (= a{j} {bv(a)}))',f'(assert (= b{j} {bv(b)}))',
                     f'(assert (= o{j} {str(op=="or").lower()}))']
    text.append(f'(assert (= v{n-1+gate_count} {bv(target,bits)}))')
    text.append('(check-sat)')
    return '\n'.join(text), ' '.join(f'{prefix}{j}' for j in range(gate_count) for prefix in ['a', 'b', 'o'])


def canonical_star_circuit(edges):
    gates=[]
    def add(op,a,b):
        gates.append((op,a,b));return 7+len(gates)-1
    tops=[]
    for a in range(3):
        neighbours=sorted(b for aa,b in edges if aa==a)
        assert neighbours
        leaf=neighbours[0]
        for b in neighbours[1:]:leaf=add('or',leaf,b)
        tops.append(add('and',a,leaf))
    output=tops[0]
    for top in tops[1:]:output=add('or',output,top)
    depth=[0]*7
    for _,a,b in gates:depth.append(1+max(depth[a],depth[b]))
    renamed=list(range(7))+[-1]*len(gates);result=[]
    for d in range(1,max(depth)+1):
        layer=[]
        for j,(op,a,b) in enumerate(gates):
            if depth[7+j]!=d:continue
            a,b=sorted((renamed[a],renamed[b]));assert a>=0
            layer.append((op=='or',a,b,j))
        for is_or,a,b,j in sorted(layer):
            renamed[7+j]=7+len(result);result.append(('or' if is_or else 'and',a,b))
    assert renamed[output]==7+len(result)-1
    for x in range(128):
        vals=[bool(x>>i&1) for i in range(7)];col=[1]*3+[2]*4
        for op,a,b in result:
            vals.append(vals[a] or vals[b] if op=='or' else vals[a] and vals[b])
            col.append(col[a]|col[b] if op=='or' else 0);assert col[-1]!=3
        assert vals[-1]==any(x>>a&1 and x>>b&1 for a,b in edges)
    return result


if __name__ == '__main__':
    import argparse,json
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mask',type=int,required=True)
    parser.add_argument('--gates',type=int,default=7)
    parser.add_argument('--timeout',type=int,default=300000)
    parser.add_argument('--pin',action='store_true')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    gates=args.mask.bit_count()+2 if args.pin else args.gates
    source,symbols=problem(gates,args.timeout,args.pin,args.mask)
    args.output.write_text(source+'\n')
    print(json.dumps(vars(args),default=str),flush=True)
    print('gates',gates,'smt_bytes',len(source),'known_star_full128_replay',args.pin,flush=True)
    z=ctypes.CDLL('/usr/lib/x86_64-linux-gnu/libz3.so.4')
    z.Z3_mk_config.restype=ctypes.c_void_p
    z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p
    z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
    z.Z3_del_context.argtypes=[ctypes.c_void_p];z.Z3_del_config.argtypes=[ctypes.c_void_p]
    cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);started=time.monotonic()
    answer=z.Z3_eval_smtlib2_string(ctx,source.encode()).decode();print(answer,flush=True)
    print('elapsed_seconds',time.monotonic()-started,flush=True)
    if answer.strip()=='sat':print(z.Z3_eval_smtlib2_string(ctx,('(get-value ('+symbols+'))').encode()).decode(),flush=True)
    z.Z3_del_context(ctx);z.Z3_del_config(cfg)
