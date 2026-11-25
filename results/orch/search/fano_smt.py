import ctypes
import ctypes.util
import json
import sys
import time
from pathlib import Path

root = Path('/tmp/oec/pequalnp-pilot-138/semantic')
tests = [int(x) for x in (root / 'constraints.txt').read_text().split()]
assert len(tests) == 58
width = len(tests)
count = int(sys.argv[1]) if len(sys.argv) > 1 else 26
seconds = int(sys.argv[2]) if len(sys.argv) > 2 else 180
job = f'fano-{count}'
fixed = len(sys.argv) > 3 and sys.argv[3] == 'fixed'
anchor = len(sys.argv) > 3 and sys.argv[3] == 'anchor'
if fixed:
    job += '-fixed'
if anchor:
    job += '-anchor'
source = ['(set-logic QF_BV)', f'(set-option :timeout {seconds * 1000})',
          '(set-option :produce-models true)', '(set-option :smt.random_seed 138)']
def bv(n, w=6):
    return f'(_ bv{n} {w})'
for i in range(14):
    val = sum(1 << j for j, t in enumerate(tests) if t >> i & 1)
    source.append(f'(define-fun v{i} () (_ BitVec {width}) {bv(val, width)})')
for j in range(count):
    n = 14 + j
    source += [f'(declare-const a{j} (_ BitVec 6))', f'(declare-const b{j} (_ BitVec 6))',
               f'(declare-const op{j} Bool)',
               f'(assert (bvult a{j} b{j}))', f'(assert (bvult b{j} {bv(n)}))']
    for sel in ['a', 'b']:
        expr = f'v{n-1}'
        for i in range(n-2, -1, -1):
            expr = f'(ite (= {sel}{j} {bv(i)}) v{i} {expr})'
        source.append(f'(define-fun {sel}v{j} () (_ BitVec {width}) {expr})')
    source += [f'(define-fun v{n} () (_ BitVec {width}) (ite op{j} (bvand av{j} bv{j}) (bvor av{j} bv{j})))',
               f'(assert (distinct v{n} av{j} bv{j}))']
for j in range(count-1):
    uses = [f'(= {side}{k} {bv(14+j)})' for k in range(j+1,count) for side in ['a','b']]
    source.append('(assert (or ' + ' '.join(uses) + '))')
if fixed:
    gates = []
    stars = []
    for l in range(7):
        p = [l, (l+1)%7, (l+3)%7]
        n = 14+len(gates)
        gates += [(p[0],p[1],False),(n,p[2],False),(n+1,7+l,True)]
        stars.append(n+2)
    out = stars[0]
    for star in stars[1:]:
        gates.append((out,star,False))
        out = 13+len(gates)
    assert len(gates) == count
    for j, (a,b,op) in enumerate(gates):
        a,b = sorted([a,b])
        source += [f'(assert (= a{j} {bv(a)}))', f'(assert (= b{j} {bv(b)}))',
                   f'(assert (= op{j} {str(op).lower()}))']
if anchor:
    source += ['(assert (not op0))', f'(assert (= a0 {bv(0)}))', f'(assert (= b0 {bv(1)}))']
    for j in range(count-1):
        independent = f'(not (= b{j+1} {bv(14+j)}))'
        colex = f'(or (bvult b{j} b{j+1}) (and (= b{j} b{j+1}) (bvule a{j} a{j+1})))'
        source.append(f'(assert (=> {independent} {colex}))')
source += [f'(assert (= v{13+count} {bv((1<<21)-1,width)}))', '(check-sat)']
model_query = '(get-value (' + ' '.join(f'a{j} b{j} op{j}' for j in range(count)) + '))'
script = '\n'.join(source) + '\n'
(root / (job + '.smt2')).write_text(script)
z3 = ctypes.CDLL(ctypes.util.find_library('z3'))
z3.Z3_mk_config.restype = ctypes.c_void_p
z3.Z3_mk_context.argtypes = [ctypes.c_void_p]
z3.Z3_mk_context.restype = ctypes.c_void_p
z3.Z3_del_config.argtypes = [ctypes.c_void_p]
z3.Z3_del_context.argtypes = [ctypes.c_void_p]
z3.Z3_eval_smtlib2_string.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
z3.Z3_eval_smtlib2_string.restype = ctypes.c_char_p
cfg = z3.Z3_mk_config()
ctx = z3.Z3_mk_context(cfg)
z3.Z3_del_config(cfg)
start = time.time()
print(f'gates={count} tests={width} timeout_s={seconds} bytes={len(script)}', flush=True)
output = z3.Z3_eval_smtlib2_string(ctx, script.encode())
print(output.decode(), flush=True)
if output.decode().strip() == 'sat':
    print(z3.Z3_eval_smtlib2_string(ctx, model_query.encode()).decode(), flush=True)
elif output.decode().strip() == 'unknown':
    print(z3.Z3_eval_smtlib2_string(ctx, b'(get-info :reason-unknown)').decode(), flush=True)
print(f'elapsed_s={time.time()-start:.3f}', flush=True)
z3.Z3_del_context(ctx)
