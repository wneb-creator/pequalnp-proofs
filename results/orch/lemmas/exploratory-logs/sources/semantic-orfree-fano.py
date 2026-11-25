from pathlib import Path
import ctypes
import re
import sys
import time


def problem(or_count=4, timeout=300000, pin=False):
    n = 14
    lines = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
    edges = [(a, 7 + b) for b, line in enumerate(lines) for a in line]
    cases = [(1 << a) | (1 << b) for a, b in edges]
    for x in range(1 << n):
        if any(x >> a & 1 and x >> b & 1 for a, b in edges):
            continue
        if any(not (x >> v & 1) and not any((a == v and x >> b & 1) or
                (b == v and x >> a & 1) for a, b in edges) for v in range(n)):
            continue
        cases.append(x)
    assert len(cases) == 58
    mask = (1 << 64) - 1
    inputs = [sum(1 << k for k, x in enumerate(cases) if x >> i & 1) for i in range(n)]
    target = sum(1 << k for k, x in enumerate(cases) if any(x >> a & 1 and x >> b & 1 for a, b in edges))
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
        assert or_count == 20
        gate_inputs = []
        for a in range(7):
            neighbors = [b for aa, b in edges if aa == a]
            gate_inputs.append(([neighbors[0]], [neighbors[1]]))
            gate_inputs.append(([n + 2*a], [neighbors[2]]))
        gate_inputs.append(([0, n+1], [1, n+3]))
        for a in range(2, 7):
            gate_inputs.append(([n + len(gate_inputs) - 1], [a, n+2*a+1]))
        gate_inputs = [tuple(sorted(operands, key=lambda term: sum(1 << i for i in term))) for operands in gate_inputs]
        for j, operands in enumerate(gate_inputs):
            for side, selected in enumerate(operands):
                for i in range(n+j):
                    name = f's{j}_{side}_{i}'
                    text.append(f'(assert {name})' if i in selected else f'(assert (not {name}))')
        for i in range(n+or_count):
            text.append(f'(assert out_{i})' if i == n + or_count - 1 else f'(assert (not out_{i}))')
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
    print('Fano inputs14 OR gates', count, 'AND gates unbounded; exact58-case monotone semantics;', 'pinned', pin, flush=True)
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
        full_inputs = [sum(1 << x for x in range(1 << 14) if x >> i & 1) for i in range(14)]
        full_wires = list(full_inputs)
        fullmask = (1 << (1 << 14)) - 1
        for operands in gates:
            terms = []
            for operand in operands:
                value = fullmask
                for i in operand:
                    value &= full_wires[i]
                terms.append(value)
            full_wires.append(terms[0] | terms[1])
        value = fullmask
        for i in selected:
            value &= full_wires[i]
        lines = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
        full_target = 0
        for b, line in enumerate(lines):
            for a in line:
                full_target |= full_inputs[a] & full_inputs[7+b]
        assert value == full_target, 'model fails full16384-row replay'
        print('Independent full16384-row replay passed:', gates, 'output conjunction', selected, flush=True)
    z.Z3_del_context(ctx)
    z.Z3_del_config(cfg)
