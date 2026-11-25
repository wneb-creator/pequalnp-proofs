from pathlib import Path
import ctypes
import sys
import time


def problem(gate_count=26, timeout=300000, or_cap=None):
    lines = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
    edges = [(a, 7 + b) for b, line in enumerate(lines) for a in line]
    cases = [(1 << a) | (1 << b) for a, b in edges]
    for s in range(1 << 14):
        if any(s >> a & 1 and s >> b & 1 for a, b in edges):
            continue
        if any(not (s >> v & 1) and not any(
                (a == v and s >> b & 1) or (b == v and s >> a & 1)
                for a, b in edges) for v in range(14)):
            continue
        cases.append(s)
    assert len(cases) == 58
    width = (14 + gate_count).bit_length()

    def bv(value, bits=width):
        return f'(_ bv{value} {bits})'

    def mux(selector, prefix, count):
        term = f'{prefix}{count - 1}'
        for k in reversed(range(count - 1)):
            term = f'(ite (= {selector} {bv(k)}) {prefix}{k} {term})'
        return term

    text = ['(set-option :produce-models true)', f'(set-option :timeout {timeout})',
            '(set-option :memory_max_size 2000)', '(set-logic QF_BV)']
    for i in range(14):
        value = sum(1 << k for k, s in enumerate(cases) if s >> i & 1)
        text += [f'(define-fun v{i} () (_ BitVec 58) {bv(value, 58)})',
                 f'(define-fun c{i} () (_ BitVec 2) {bv(1 if i < 7 else 2, 2)})']
    for j in range(gate_count):
        text += [f'(declare-const a{j} (_ BitVec {width}))',
                 f'(declare-const b{j} (_ BitVec {width}))',
                 f'(declare-const o{j} Bool)',
                 f'(declare-const v{14+j} (_ BitVec 58))',
                 f'(declare-const c{14+j} (_ BitVec 2))']
    for j in range(gate_count):
        w = 14 + j
        text += [f'(assert (bvult a{j} {bv(w)}))', f'(assert (bvult b{j} {bv(w)}))',
                 f'(assert (bvule a{j} b{j}))',
                 f'(assert (=> o{j} (distinct a{j} b{j})))']
        for selector in [f'a{j}', f'b{j}']:
            text += [f'(define-fun {selector}v () (_ BitVec 58) {mux(selector, "v", w)})',
                     f'(define-fun {selector}c () (_ BitVec 2) {mux(selector, "c", w)})']
        text += [f'(assert (= v{w} (ite o{j} (bvor a{j}v b{j}v) (bvand a{j}v b{j}v))))',
                 f'(assert (= c{w} (ite o{j} (bvor a{j}c b{j}c) {bv(0, 2)})))',
                 f'(assert (distinct c{w} {bv(3, 2)}))']
        if j + 1 < gate_count:
            uses = ' '.join(f'(= {selector}{k} {bv(w)})'
                            for k in range(j + 1, gate_count) for selector in ['a', 'b'])
            text.append(f'(assert (or {uses}))')
    if or_cap is not None:
        bits = gate_count.bit_length()
        terms = [f'(ite o{j} {bv(1, bits)} {bv(0, bits)})' for j in range(gate_count)]
        total = '(bvadd ' + ' '.join(terms) + ')'
        text.append(f'(assert (bvule {total} {bv(or_cap, bits)}))')
    text.append(f'(assert (= v{13 + gate_count} {bv((1 << 21) - 1, 58)}))')
    text.append('(check-sat)')
    return '\n'.join(text), ' '.join(f'{prefix}{j}' for j in range(gate_count) for prefix in ['a', 'b', 'o'])


if __name__ == '__main__':
    gates = int(sys.argv[1]) if len(sys.argv) > 1 else 26
    timeout = int(sys.argv[2]) if len(sys.argv) > 2 else 300000
    or_cap = int(sys.argv[3]) if len(sys.argv) > 3 else None
    output = Path(sys.argv[4]) if len(sys.argv) > 4 else Path('/tmp/oec/pequalnp-pilot-163/fano.smt2')
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
