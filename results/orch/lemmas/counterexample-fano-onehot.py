from pathlib import Path
import ctypes
import sys
import time


def problem(gates=26, timeout=600000, dirty=True, pinned=False):
    lines = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
    edges = [(a, 7 + b) for b, row in enumerate(lines) for a in row]
    cases = [(1 << a) | (1 << b) for a, b in edges]
    for A in range(1 << 7):
        B = sum(1 << b for b, row in enumerate(lines) if all(not (A >> a & 1) for a in row))
        closed = sum(1 << a for a in range(7)
                     if all(not (B >> b & 1) for b, row in enumerate(lines) if a in row))
        if closed == A:
            cases.append(A | (B << 7))
    assert len(cases) == 58
    target = (1 << 21) - 1

    def bv(value, bits):
        return f'(_ bv{value} {bits})'

    text = ['(set-option :produce-models true)', f'(set-option :timeout {timeout})',
            '(set-option :memory_max_size 2500)', '(set-logic QF_BV)']
    for i in range(14):
        value = sum(1 << k for k, s in enumerate(cases) if s >> i & 1)
        text += [f'(define-fun v{i} () (_ BitVec 58) {bv(value, 58)})',
                 f'(define-fun c{i} () (_ BitVec 2) {bv(1 if i < 7 else 2, 2)})']
    for j in range(gates):
        text += [f'(declare-const o{j} Bool)', f'(declare-const v{14+j} (_ BitVec 58))',
                 f'(declare-const c{14+j} (_ BitVec 2))']
        for side in ['a', 'b']:
            text += [f'(declare-const {side}{j}v (_ BitVec 58))',
                     f'(declare-const {side}{j}c (_ BitVec 2))',
                     f'(declare-const {side}{j}i (_ BitVec 6))']
            text += [f'(declare-const {side}{j}_{k} Bool)' for k in range(14 + j)]
    for j in range(gates):
        for side in ['a', 'b']:
            names = ' '.join(f'{side}{j}_{k}' for k in range(14 + j))
            text += [f'(assert (or {names}))', f'(assert ((_ at-most 1) {names}))']
            for k in range(14 + j):
                text.append(f'(assert (=> {side}{j}_{k} (and (= {side}{j}v v{k}) '
                            f'(= {side}{j}c c{k}) (= {side}{j}i {bv(k, 6)}))))')
        text += [f'(assert (bvule a{j}i b{j}i))',
                 f'(assert (=> o{j} (distinct a{j}i b{j}i)))',
                 f'(assert (= v{14+j} (ite o{j} (bvor a{j}v b{j}v) (bvand a{j}v b{j}v))))',
                 f'(assert (= c{14+j} (ite o{j} (bvor a{j}c b{j}c) {bv(0, 2)})))',
                 f'(assert (distinct c{14+j} {bv(3, 2)}))']
        if j + 1 < gates:
            uses = ' '.join(f'{side}{k}_{14+j}' for k in range(j + 1, gates) for side in ['a', 'b'])
            text.append(f'(assert (or {uses}))')
    if gates == 26:
        text.append('(assert ((_ at-most 19) ' + ' '.join(f'o{j}' for j in range(gates)) + '))')
    if dirty:
        mask = ((1 << 58) - 1) ^ target
        choices = ' '.join(f'(and (not o{j}) (distinct (bvand v{14+j} {bv(mask,58)}) {bv(0,58)}))'
                           for j in range(gates))
        text.append(f'(assert (or {choices}))')
    text.append(f'(assert (= v{13+gates} {bv(target,58)}))')
    if pinned:
        assert gates == 27 and not dirty
        fixed = []
        outputs = []
        for a in range(7):
            leaves = [7 + b for b, row in enumerate(lines) if a in row]
            w = 14 + len(fixed)
            fixed += [(leaves[0], leaves[1], True), (w, leaves[2], True), (a, w + 1, False)]
            outputs.append(w + 2)
        while len(outputs) > 1:
            a, b = outputs.pop(), outputs.pop()
            outputs.append(14 + len(fixed))
            fixed.append((a, b, True))
        for j, (a, b, op) in enumerate(fixed):
            a, b = sorted([a, b])
            text += [f'(assert a{j}_{a})', f'(assert b{j}_{b})', f'(assert (= o{j} {str(op).lower()}))']
    text.append('(check-sat)')
    symbols = ' '.join(f'{side}{j}i' for j in range(gates) for side in ['a', 'b'])
    symbols += ' ' + ' '.join(f'o{j}' for j in range(gates))
    return '\n'.join(text), symbols


if __name__ == '__main__':
    pinned = len(sys.argv) > 1 and sys.argv[1] == 'validate'
    source, symbols = problem(27 if pinned else 26, 5000 if pinned else 600000,
                              dirty=not pinned, pinned=pinned)
    name = 'fano-onehot-known27' if pinned else 'fano-onehot26'
    Path('/tmp/oec/pequalnp-pilot-163', name + '.smt2').write_text(source + '\n')
    print('Generated', name, len(source), 'bytes', flush=True)
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
        print(z.Z3_eval_smtlib2_string(ctx, ('(get-value (' + symbols + '))').encode()).decode(), flush=True)
    z.Z3_del_context(ctx)
    z.Z3_del_config(cfg)
