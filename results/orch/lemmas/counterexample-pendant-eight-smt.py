"""Any at-most-eight-gate T0 circuit for the7-input C6+pendant target.

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


def problem(gate_count=8, timeout=900000, pinned=False):
    p = 3
    n = 7
    edges = [(a, 3 + b) for a in range(3) for b in range(3) if a != b] + [(0, 6)]
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
            '(set-option :memory_max_size 2000)', '(set-logic QF_BV)']
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
        # Star cover at point inputs0,1,2; canonical layer order.
        known=[('or',3,4),('or',3,5),('or',4,5),('and',1,8),
               ('and',2,7),('or',6,9),('and',0,12),('or',10,11),('or',13,14)]
        assert gate_count==9
        for j,(op,a,b) in enumerate(known):
            a,b=sorted((a,b))
            text += [f'(assert (= a{j} {bv(a)}))',f'(assert (= b{j} {bv(b)}))',
                     f'(assert (= o{j} {str(op=="or").lower()}))']
    text.append(f'(assert (= v{n-1+gate_count} {bv(target,bits)}))')
    text.append('(check-sat)')
    return '\n'.join(text), ' '.join(f'{prefix}{j}' for j in range(gate_count) for prefix in ['a', 'b', 'o'])


if __name__ == '__main__':
    validate = len(sys.argv)>1 and sys.argv[1]=='validate'
    gates = 9 if validate else (int(sys.argv[1]) if len(sys.argv)>1 else 8)
    timeout = 10000 if validate else (int(sys.argv[2]) if len(sys.argv)>2 else 900000)
    output = Path(sys.argv[3]) if len(sys.argv)>3 else Path('/tmp/oec/pequalnp-pilot-163/counterexample-pendant-'+('known9' if validate else 'eight')+'.smt2')
    source, symbols = problem(gates, timeout, pinned=validate)
    output.write_text(source + '\n')
    print('Generated', gates, 'gates;', len(source), 'SMT bytes;', 'known9_pinned', validate, flush=True)
    z = ctypes.CDLL('/usr/lib/x86_64-linux-gnu/libz3.so.4')
    z.Z3_mk_config.restype = ctypes.c_void_p
    z.Z3_mk_context.argtypes = [ctypes.c_void_p]
    z.Z3_mk_context.restype = ctypes.c_void_p
    z.Z3_eval_smtlib2_string.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
    z.Z3_eval_smtlib2_string.restype = ctypes.c_char_p
    z.Z3_del_context.argtypes = [ctypes.c_void_p]
    z.Z3_del_config.argtypes = [ctypes.c_void_p]
    cfg = z.Z3_mk_config()
    ctx = z.Z3_mk_context(cfg)
    started = time.monotonic()
    answer = z.Z3_eval_smtlib2_string(ctx, source.encode()).decode()
    print(answer, flush=True)
    print('Elapsed seconds', time.monotonic() - started, flush=True)
    if answer.strip() == 'sat':
        model = z.Z3_eval_smtlib2_string(ctx, ('(get-value (' + symbols + '))').encode()).decode()
        print(model, flush=True)
    z.Z3_del_context(ctx)
    z.Z3_del_config(cfg)
