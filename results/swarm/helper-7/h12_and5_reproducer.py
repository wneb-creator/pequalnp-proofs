"""Fixed H12 AND<=5 query; source data for independent review.

No minimum-count pruning. Free OR regions are arbitrary source subsets.
Unused false AND gates pad smaller circuits. Common free-OR sources can be
factored from both operands and restored at every later use, so selector
sets may be disjoint. Greedy ready-gate ordering gives the colex constraint.
Positive edge rows and maximal-independent negative rows determine this
monotone graph function. Output is a free OR of arbitrary source wires.
"""
import argparse
import hashlib
from pathlib import Path

N, K = 12, 5
EDGES = [(0,4),(0,5),(1,3),(1,5),(2,3),(2,4),(0,6),(6,7),(7,3),
         (1,8),(8,9),(9,4),(2,10),(10,11),(11,5)]
EXPECTED_SHA256 = 'feba8ebfee2d453ead6a6e1cda8a90d317d70aef341349ed1d046cb60daf1499'

def generate():
    positive = sorted({(1<<a)|(1<<b) for a,b in EDGES})
    negative = []
    for row in range(1<<N):
        if any(row&e == e for e in positive):
            continue
        if all(row&(1<<v) or any(((row|(1<<v))&e)==e for e in positive) for v in range(N)):
            negative.append(row)
    assert len(positive)==15 and len(negative)==26
    rows = positive+negative
    bits, width = len(rows), N+K
    q = ['(set-logic QF_BV)', '(set-option :timeout 1200000)', '(set-option :produce-models true)']
    for i in range(N):
        value = sum(1<<j for j,row in enumerate(rows) if row&(1<<i))
        q.append(f'(define-fun v{i} () (_ BitVec {bits}) (_ bv{value} {bits}))')
    neutral = f'(_ bv0 {bits})'
    def aggregate(label,end):
        term, mask = neutral, f'(_ bv0 {width})'
        for j in range(end):
            name=f'{label}_{j}'
            q.append(f'(declare-const {name} Bool)')
            term=f'(bvor {term} (ite {name} v{j} {neutral}))'
            mask=f'(bvor {mask} (ite {name} (_ bv{1<<j} {width}) (_ bv0 {width})))'
        q.append(f'(define-fun mask_{label} () (_ BitVec {width}) {mask})')
        return term
    for i in range(K):
        left=aggregate(f'l{i}',N+i)
        right=aggregate(f'r{i}',N+i)
        q.append(f'(declare-const v{N+i} (_ BitVec {bits}))')
        q.append(f'(assert (= v{N+i} (bvand {left} {right})))')
        rankwidth=(N+K+1).bit_length()
        rank=f'(_ bv0 {rankwidth})'
        for j in range(N+i):
            rank=f'(ite (or l{i}_{j} r{i}_{j}) (_ bv{j+1} {rankwidth}) {rank})'
        q.append(f'(define-fun rank{i} () (_ BitVec {rankwidth}) {rank})')
        q.append(f'(assert (= (bvand mask_l{i} mask_r{i}) (_ bv0 {width})))')
        q.append(f'(assert (bvule mask_l{i} mask_r{i}))')
        if i:
            ordered=f'(or (bvult rank{i-1} rank{i}) (and (= rank{i-1} rank{i}) (or (bvult mask_l{i-1} mask_l{i}) (and (= mask_l{i-1} mask_l{i}) (bvule mask_r{i-1} mask_r{i})))))'
            q.append(f'(assert {ordered})')
    output=aggregate('out',N+K)
    q.append(f'(assert (= {output} (_ bv{(1<<len(positive))-1} {bits})))')
    q.append('(check-sat)')
    return '\n'.join(q)+'\n'

if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--solve',action='store_true')
    args=parser.parse_args()
    source=generate().encode()
    digest=hashlib.sha256(source).hexdigest()
    assert digest==EXPECTED_SHA256
    args.output.write_bytes(source)
    print('SMT_SHA256',digest,'bytes',len(source),flush=True)
    if args.solve:
        import ctypes
        import ctypes.util
        import time
        lib=ctypes.CDLL(ctypes.util.find_library('z3'))
        lib.Z3_mk_config.restype=ctypes.c_void_p
        lib.Z3_mk_context.argtypes=[ctypes.c_void_p]
        lib.Z3_mk_context.restype=ctypes.c_void_p
        lib.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p]
        lib.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
        lib.Z3_del_context.argtypes=[ctypes.c_void_p]
        lib.Z3_del_config.argtypes=[ctypes.c_void_p]
        cfg=lib.Z3_mk_config()
        ctx=lib.Z3_mk_context(cfg)
        started=time.monotonic()
        status=lib.Z3_eval_smtlib2_string(ctx,source).decode().strip()
        print('STATUS',status,'seconds',time.monotonic()-started,flush=True)
        lib.Z3_del_context(ctx)
        lib.Z3_del_config(cfg)
