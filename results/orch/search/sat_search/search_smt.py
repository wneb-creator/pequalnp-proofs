#!/usr/bin/env python3
"""Bounded-edit exact synthesis for the Fano incidence function.

Only AND/OR gates are used. The 21 minimal positive and 37 maximal negative
assignments characterize the monotone truth table; every model is additionally
verified against all 2^14 inputs before a witness is written.
"""
import argparse
import ctypes
import datetime
import json
from pathlib import Path
import re
import time


def solver_api(timeout_ms, memory_mb):
    z = ctypes.CDLL('/usr/lib/x86_64-linux-gnu/libz3.so.4')
    P, S, I, U = ctypes.c_void_p, ctypes.c_char_p, ctypes.c_int, ctypes.c_uint
    sigs = {
        'Z3_get_full_version': ([], S),
        'Z3_mk_config': ([], P),
        'Z3_del_config': ([P], None),
        'Z3_mk_context': ([P], P),
        'Z3_del_context': ([P], None),
        'Z3_mk_solver': ([P], P),
        'Z3_solver_inc_ref': ([P, P], None),
        'Z3_solver_dec_ref': ([P, P], None),
        'Z3_solver_from_string': ([P, P, S], None),
        'Z3_solver_check': ([P, P], I),
        'Z3_solver_get_reason_unknown': ([P, P], S),
        'Z3_solver_get_model': ([P, P], P),
        'Z3_model_to_string': ([P, P], S),
        'Z3_mk_params': ([P], P),
        'Z3_params_inc_ref': ([P, P], None),
        'Z3_params_dec_ref': ([P, P], None),
        'Z3_mk_string_symbol': ([P, S], P),
        'Z3_params_set_uint': ([P, P, P, U], None),
        'Z3_solver_set_params': ([P, P, P], None),
        'Z3_global_param_set': ([S, S], None),
    }
    for name, (args, ret) in sigs.items():
        fun = getattr(z, name)
        fun.argtypes = args
        fun.restype = ret
    z.Z3_global_param_set(b'memory_max_size', str(memory_mb).encode())
    cfg = z.Z3_mk_config()
    ctx = z.Z3_mk_context(cfg)
    z.Z3_del_config(cfg)
    solver = z.Z3_mk_solver(ctx)
    z.Z3_solver_inc_ref(ctx, solver)
    params = z.Z3_mk_params(ctx)
    z.Z3_params_inc_ref(ctx, params)
    z.Z3_params_set_uint(ctx, params,
                         z.Z3_mk_string_symbol(ctx, b'timeout'), timeout_ms)
    z.Z3_solver_set_params(ctx, solver, params)
    z.Z3_params_dec_ref(ctx, params)
    return z, ctx, solver


def build_smt(cases, gates, edits, free_gates=None, selector_kind='bv',
              allow_repeat=False, canonical=False, connected=False):
    samples = cases['positive'] + cases['negative']
    width = len(samples)
    lit = lambda n: f'(_ bv{n} {width})'
    sel_lit = lambda n: f'(_ bv{n} 6)' if selector_kind == 'bv' else str(n)
    sel_type = '(_ BitVec 6)' if selector_kind == 'bv' else 'Int'
    less = 'bvult' if selector_kind == 'bv' else '<'
    leq = 'bvule' if selector_kind == 'bv' else '<='
    lines = [f'(set-logic {"QF_BV" if selector_kind == "bv" else "QF_UFBVLIA"})']
    for w in range(14):
        bits = sum(((x >> w) & 1) << t for t, x in enumerate(samples))
        lines.append(f'(define-fun v{w} () (_ BitVec {width}) {lit(bits)})')
    changed = []
    for i, (old_op, old_a, old_b) in enumerate(gates):
        w = 14 + i
        old_a, old_b = sorted((old_a, old_b))
        for part in ('a', 'b'):
            lines.append(f'(declare-const {part}{i} {sel_type})')
            lines.append(f'(assert ({less} {part}{i} {sel_lit(w)}))')
            if selector_kind == 'int':
                lines.append(f'(assert (<= 0 {part}{i}))')
        lines.append(f'(assert ({leq if allow_repeat else less} a{i} b{i}))')
        lines.append(f'(declare-const o{i} Bool)')
        for part in ('a', 'b'):
            expr = f'v{w-1}'
            for q in range(w-2, -1, -1):
                expr = f'(ite (= {part}{i} {sel_lit(q)}) v{q} {expr})'
            lines.append(f'(define-fun {part}v{i} () (_ BitVec {width}) {expr})')
        lines.append(f'(declare-const v{w} (_ BitVec {width}))')
        lines.append(f'(assert (= v{w} (ite o{i} (bvor av{i} bv{i}) (bvand av{i} bv{i}))))')
        same = f'(and (= a{i} {sel_lit(old_a)}) (= b{i} {sel_lit(old_b)}) (= o{i} {str(bool(old_op)).lower()}))'
        lines.append(f'(define-fun c{i} () Bool (not {same}))')
        changed.append(f'c{i}')
        if free_gates is not None and i not in free_gates:
            lines.append(f'(assert {same})')
    if canonical:
        for i in range(len(gates)-1):
            j = i+1
            lines.append(f'(assert ({leq} b{i} b{j}))')
            lines.append(f'(assert (=> (= b{i} b{j}) ({leq} a{i} a{j})))')
            lines.append(f'(assert (=> (and (= b{i} b{j}) (= a{i} a{j})) (or (not o{i}) o{j})))')
    if connected:
        for i in range(len(gates)-1):
            consumers = [f'(= {part}{j} {sel_lit(14+i)})'
                         for j in range(i+1, len(gates)) for part in ('a','b')]
            lines.append(f'(assert (or {" ".join(consumers)}))')
    target = (1 << len(cases['positive'])) - 1
    lines.append(f'(assert (= v{13+len(gates)} {lit(target)}))')
    if edits is not None:
        if edits == 0:
            lines.extend(f'(assert (not {name}))' for name in changed)
        else:
            bits = len(gates).bit_length()
            total = f'(_ bv0 {bits})'
            for name in changed:
                total = f'(bvadd {total} (ite {name} (_ bv1 {bits}) (_ bv0 {bits})))'
            lines.append(f'(assert (bvule {total} (_ bv{edits} {bits})))')
    return '\n'.join(lines) + '\n'


def parse_model(model, count):
    # The C API prints declarations as name -> value, with bitvectors usually hex.
    vals = {}
    for name, value in re.findall(r'\b([abo][0-9]+) -> ([^\n]+)', model):
        value = value.strip()
        if value in ('true', 'false'):
            vals[name] = value == 'true'
        elif value.startswith('#b'):
            vals[name] = int(value[2:], 2)
        elif value.startswith('#x'):
            vals[name] = int(value[2:], 16)
        elif re.fullmatch(r'[0-9]+', value):
            vals[name] = int(value)
        else:
            match = re.fullmatch(r'\(_ bv([0-9]+) [0-9]+\)', value)
            if match:
                vals[name] = int(match.group(1))
    return [[int(vals[f'o{i}']), vals[f'a{i}'], vals[f'b{i}']]
            for i in range(count)]


def verify(cases, gates):
    errors = []
    for x in range(1 << 14):
        values = [(x >> i) & 1 for i in range(14)]
        for op, a, b in gates:
            values.append(values[a] | values[b] if op else values[a] & values[b])
        target = any((x >> p) & (x >> l) & 1 for p, l in cases['edges'])
        if values[-1] != target:
            errors.append(x)
    return errors


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cases', type=Path, required=True)
    ap.add_argument('--base', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--edits', type=int)
    ap.add_argument('--free', type=str)
    ap.add_argument('--timeout', type=int, default=180)
    ap.add_argument('--memory', type=int, default=768)
    ap.add_argument('--selector', choices=('bv','int'), default='bv')
    ap.add_argument('--allow-repeat', action='store_true')
    ap.add_argument('--canonical', action='store_true')
    ap.add_argument('--connected', action='store_true')
    args = ap.parse_args()
    cases = json.loads(args.cases.read_text())
    base = json.loads(args.base.read_text())
    gates = base['gates'] if isinstance(base, dict) else base
    free = {int(i) for i in args.free.split(',')} if args.free else None
    args.out.mkdir(parents=True, exist_ok=True)
    smt = build_smt(cases, gates, args.edits, free, args.selector,
                    args.allow_repeat, args.canonical, args.connected)
    (args.out/'problem.smt2').write_text(smt)
    z, ctx, solver = solver_api(args.timeout*1000, args.memory)
    print('started', datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'z3', z.Z3_get_full_version().decode(), 'edits', args.edits,
          'free', sorted(free) if free else 'all', flush=True)
    start = time.monotonic()
    z.Z3_solver_from_string(ctx, solver, smt.encode())
    status = z.Z3_solver_check(ctx, solver)
    result = {'status': {1:'sat',-1:'unsat',0:'unknown'}[status],
              'seconds': time.monotonic()-start, 'edits':args.edits,
              'free': sorted(free) if free else None,
              'gate_count':len(gates), 'allow_repeat':args.allow_repeat,
              'canonical':args.canonical,'connected':args.connected}
    if status == 1:
        model = z.Z3_model_to_string(ctx, z.Z3_solver_get_model(ctx, solver)).decode()
        (args.out/'model.txt').write_text(model)
        candidate = parse_model(model, len(gates))
        errors = verify(cases, candidate)
        result.update(gates=candidate, exhaustive_errors=errors,
                      verified_assignments=1<<14)
        if not errors:
            filename = 'WITNESS.json' if len(gates)<27 else 'baseline-verified.json'
            (args.out/filename).write_text(json.dumps(result, indent=2)+'\n')
    elif status == 0:
        result['reason'] = z.Z3_solver_get_reason_unknown(ctx, solver).decode()
    (args.out/'result.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result), flush=True)
    z.Z3_solver_dec_ref(ctx, solver)
    z.Z3_del_context(ctx)


if __name__ == '__main__':
    main()
