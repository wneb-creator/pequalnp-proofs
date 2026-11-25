from pathlib import Path
import ctypes
import re
import sys
import time


def problem(or_count=4, timeout=300000, pin=False):
    n = 6
    rows = 1 << n
    mask = (1 << rows) - 1
    edges = [(a, 3 + b) for a in range(3) for b in range(3) if a != b]
    inputs = [sum(1 << x for x in range(rows) if x >> i & 1) for i in range(n)]
    target = sum(1 << x for x in range(rows) if any(x >> a & 1 and x >> b & 1 for a, b in edges))
    bv = lambda value: '#x' + format(value, '016x')
    text = ['(set-option :produce-models true)', f'(set-option :timeout {timeout})',
            '(set-option :memory_max_size 2000)', '(set-logic QF_BV)']
    symbols = []
    for i, value in enumerate(inputs):
        text.append(f'(define-fun v{i} () (_ BitVec 64) {bv(value)})')
    for j in range(or_count):
        text.append(f'(declare-const v{n+j} (_ BitVec 64))')
        for side in range(2):
            for i in range(n + j):
                name = f's{j}_{side}_{i}'
                symbols.append(name)
                text.append(f'(declare-const {name} Bool)')
    for i in range(n + or_count):
        name = f'out_{i}'
        symbols.append(name)
        text.append(f'(declare-const {name} Bool)')

    def conjunction(names):
        terms = [f'(ite {name} v{i} {bv(mask)})' for i, name in enumerate(names)]
        result = terms[0]
        for term in terms[1:]:
            result = f'(bvand {result} {term})'
        text.append('(assert (or ' + ' '.join(names) + '))')
        return result

    def selector_mask(names):
        result = f'(ite {names[-1]} #b1 #b0)'
        for name in reversed(names[:-1]):
            result = f'(concat {result} (ite {name} #b1 #b0))'
        return result

    for j in range(or_count):
        names = [[f's{j}_{side}_{i}' for i in range(n+j)] for side in range(2)]
        operands = [conjunction(ns) for ns in names]
        text.append(f'(assert (= v{n+j} (bvor {operands[0]} {operands[1]})))')
        text.append(f'(assert (bvule {selector_mask(names[0])} {selector_mask(names[1])}))')
    text.append(f'(assert (= {conjunction([f"out_{i}" for i in range(n+or_count)])} {bv(target)}))')
    if pin:
        assert or_count == 5
        gate_inputs = [([4], [5]), ([3], [5]), ([3], [4]), ([0, 6], [1, 7]), ([2, 8], [9])]
        for j, operands in enumerate(gate_inputs):
            for side, selected in enumerate(operands):
                for i in range(n+j):
                    name = f's{j}_{side}_{i}'
                    text.append(f'(assert {name})' if i in selected else f'(assert (not {name}))')
        for i in range(n+or_count):
            text.append(f'(assert out_{i})' if i == 10 else f'(assert (not out_{i}))')
    text.append('(check-sat)')
    return '\n'.join(text), symbols, inputs, target


def validate_model(model, count, inputs, target):
    chosen = {name: value == 'true' for name, value in re.findall(r'\((s\d+_\d+_\d+|out_\d+)\s+(true|false)\)', model)}
    n = len(inputs)
    wires = list(inputs)
    gates = []
    full = (1 << (1 << n)) - 1
    for j in range(count):
        terms = []
        selections = []
        for side in range(2):
            selected = [i for i in range(n+j) if chosen[f's{j}_{side}_{i}']]
            assert selected
            value = full
            for i in selected:
                value &= wires[i]
            selections.append(selected)
            terms.append(value)
        wires.append(terms[0] | terms[1])
        gates.append(selections)
    selected = [i for i in range(n+count) if chosen[f'out_{i}']]
    assert selected
    value = full
    for i in selected:
        value &= wires[i]
    assert value == target, 'model fails full truth-table replay'
    return gates, selected


if __name__ == '__main__':
    count = int(sys.argv[1])
    timeout = int(sys.argv[2])
    output = Path(sys.argv[3])
    pin = len(sys.argv) > 4 and sys.argv[4] == 'pin'
    source, symbols, inputs, target = problem(count, timeout, pin)
    output.write_text(source + '\n')
    print('C6 inputs6 OR gates', count, 'AND gates unbounded; full64-row semantics;', 'pinned', pin, flush=True)
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
    print('Elapsed seconds', time.monotonic()-started, flush=True)
    if answer.strip() == 'sat':
        model = z.Z3_eval_smtlib2_string(ctx, ('(get-value (' + ' '.join(symbols) + '))').encode()).decode()
        output.with_suffix('.model').write_text(model)
        gates, selected = validate_model(model, count, inputs, target)
        print('Independent full-table replay passed:', gates, 'output conjunction', selected, flush=True)
    z.Z3_del_context(ctx)
    z.Z3_del_config(cfg)
