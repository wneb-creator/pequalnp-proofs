from pathlib import Path
import ctypes
import sys
import time


def problem(gate_count=9, timeout=300000, or_cap=None):
    p = 3
    n = 7
    edges = [(a, 3 + b) for a in range(3) for b in range(3) if a != b] + [(0, 6)]
    cases = list(range(128))
    target = sum(1 << s for s in cases if any(s >> a & 1 and s >> b & 1 for a, b in edges))
    edge_mask = sum(1 << ((1 << a) | (1 << b)) for a, b in edges)
    negative_mask = ((1 << len(cases)) - 1) ^ target
    dirty = sum(1 << s for s in cases if s.bit_count() <= 2 and not (target >> s & 1))
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
                 f'(define-fun h{i} () (_ BitVec {gate_count}) {bv(0, gate_count)})']
    for j in range(gate_count):
        text += [f'(declare-const a{j} (_ BitVec {width}))',
                 f'(declare-const b{j} (_ BitVec {width}))',
                 f'(declare-const o{j} Bool)',
                 f'(declare-const v{n+j} (_ BitVec {bits}))',
                 f'(declare-const c{n+j} (_ BitVec 2))',
                 f'(declare-const h{n+j} (_ BitVec {gate_count}))']
    for j in range(gate_count):
        w = n + j
        text += [f'(assert (bvult a{j} {bv(w)}))', f'(assert (bvult b{j} {bv(w)}))',
                 f'(assert (bvule a{j} b{j}))',
                 f'(assert (=> o{j} (distinct a{j} b{j})))']
        for selector in [f'a{j}', f'b{j}']:
            text += [f'(define-fun {selector}v () (_ BitVec {bits}) {mux(selector, "v", w)})',
                     f'(define-fun {selector}c () (_ BitVec 2) {mux(selector, "c", w)})',
                     f'(define-fun {selector}h () (_ BitVec {gate_count}) {mux(selector, "h", w)})']
        text += [f'(assert (= v{w} (ite o{j} (bvor a{j}v b{j}v) (bvand a{j}v b{j}v))))',
                 f'(assert (= c{w} (ite o{j} (bvor a{j}c b{j}c) {bv(0, 2)})))',
                 f'(assert (distinct c{w} {bv(3, 2)}))',
                 f'(assert (= h{w} (bvor (bvor a{j}h b{j}h) {bv(1 << j, gate_count)})))',
                 f'(assert (distinct (bvand v{w} {bv(edge_mask, bits)}) {bv(0, bits)}))']
        for k in range(w):
            text.append(f'(assert (not (and (= v{w} v{k}) (= (bvor c{w} c{k}) c{w}))))')
        for k in range(j):
            text.append(f'(assert (=> (and (not o{j}) (not o{k}) (= (bvand v{n+k} {bv(negative_mask, bits)}) {bv(0, bits)})) (= (bvand h{w} {bv(1 << k, gate_count)}) {bv(0, gate_count)})))')
        if j + 1 < gate_count:
            uses = ' '.join(f'(= {selector}{k} {bv(w)})'
                            for k in range(j + 1, gate_count) for selector in ['a', 'b'])
            text.append(f'(assert (or {uses}))')
    dirties = ' '.join(f'(and (not o{j}) (distinct (bvand v{n+j} {bv(dirty,bits)}) {bv(0,bits)}))' for j in range(gate_count))
    text.append(f'(assert (or {dirties}))')
    text.append(f'(assert (= v{n-1+gate_count} {bv(target,bits)}))')
    text.append('(check-sat)')
    return '\n'.join(text), ' '.join(f'{prefix}{j}' for j in range(gate_count) for prefix in ['a', 'b', 'o'])


if __name__ == '__main__':
    gates = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    timeout = int(sys.argv[2]) if len(sys.argv) > 2 else 300000
    or_cap = int(sys.argv[3]) if len(sys.argv) > 3 else None
    output = Path(sys.argv[4]) if len(sys.argv) > 4 else Path('/tmp/oec/pequalnp-pilot-163/structural-pendant-normal.smt2')
    source, symbols = problem(gates, timeout, or_cap)
    output.write_text(source + '\n')
    print('Generated', gates, 'gates;', len(source), 'SMT bytes;', 'OR cap', or_cap, flush=True)
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
