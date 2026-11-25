#!/usr/bin/env python3
"""Bounded-edit exact synthesis for the Petersen edge function.

Only AND/OR gates are used. The 15 minimal positive and 15 maximal negative
assignments characterize the monotone truth table; every model is additionally
verified against all 2^10 inputs before a witness is written.
"""
import argparse
import ctypes
import datetime
import json
from pathlib import Path
import re
import time


def solver_api(timeout_ms, memory_mb, engine='generic'):
    z = ctypes.CDLL('/usr/lib/x86_64-linux-gnu/libz3.so.4')
    P, S, I, U = ctypes.c_void_p, ctypes.c_char_p, ctypes.c_int, ctypes.c_uint
    sigs = {
        'Z3_get_full_version': ([], S),
        'Z3_mk_config': ([], P),
        'Z3_del_config': ([P], None),
        'Z3_mk_context': ([P], P),
        'Z3_del_context': ([P], None),
        'Z3_mk_solver': ([P], P),
        'Z3_mk_solver_for_logic': ([P, P], P),
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
    solver = (z.Z3_mk_solver_for_logic(ctx,z.Z3_mk_string_symbol(ctx,b'QF_BV'))
              if engine=='qfbv' else z.Z3_mk_solver(ctx))
    z.Z3_solver_inc_ref(ctx, solver)
    params = z.Z3_mk_params(ctx)
    z.Z3_params_inc_ref(ctx, params)
    z.Z3_params_set_uint(ctx, params,
                         z.Z3_mk_string_symbol(ctx, b'timeout'), timeout_ms)
    z.Z3_solver_set_params(ctx, solver, params)
    z.Z3_params_dec_ref(ctx, params)
    return z, ctx, solver


def build_smt(cases, gates, edits, free_gates=None, selector_kind='bv',
              allow_repeat=False, canonical=False, connected=False,
              first=None, positive_live=False, forbid_or='none',
              single_input=None, single_op=None, single_or_helper=False,
              essential=False, monotone_rows=False):
    n = cases.get('inputs', 10)
    samples = cases['positive'] + cases['negative']
    width = len(samples)
    lit = lambda n: f'(_ bv{n} {width})'
    sel_lit = lambda n: f'(_ bv{n} 6)' if selector_kind == 'bv' else str(n)
    sel_type = '(_ BitVec 6)' if selector_kind == 'bv' else 'Int'
    less = 'bvult' if selector_kind == 'bv' else '<'
    leq = 'bvule' if selector_kind == 'bv' else '<='
    lines = [f'(set-logic {"QF_BV" if selector_kind == "bv" else "QF_UFBVLIA"})']
    input_bits = []
    for w in range(n):
        bits = sum(((x >> w) & 1) << t for t, x in enumerate(samples))
        input_bits.append(bits)
        lines.append(f'(define-fun v{w} () (_ BitVec {width}) {lit(bits)})')
    changed = []
    for i, (old_op, old_a, old_b) in enumerate(gates):
        w = n + i
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
        if monotone_rows:
            for lo,x in enumerate(samples):
                for hi,y in enumerate(samples):
                    if x != y and x & ~y == 0:
                        lines.append(f'(assert (or (= ((_ extract {lo} {lo}) v{w}) #b0) (= ((_ extract {hi} {hi}) v{w}) #b1)))')
        if positive_live:
            pos = (1 << len(cases['positive'])) - 1
            lines.append(f'(assert (distinct (bvand v{w} {lit(pos)}) {lit(0)}))')
        if forbid_or != 'none':
            pairs = cases['edges'] if forbid_or == 'edges' else [(a,b) for a in range(n) for b in range(a+1,n)]
            masks = sorted({input_bits[a] | input_bits[b] for a,b in pairs})
            lines.extend(f'(assert (distinct v{w} {lit(mask)}))' for mask in masks)
        same = f'(and (= a{i} {sel_lit(old_a)}) (= b{i} {sel_lit(old_b)}) (= o{i} {str(bool(old_op)).lower()}))'
        lines.append(f'(define-fun c{i} () Bool (not {same}))')
        changed.append(f'c{i}')
        if free_gates is not None and i not in free_gates:
            lines.append(f'(assert {same})')
    if canonical:
        for i in range(1 if first is not None else 0, len(gates)-1):
            j = i+1
            lines.append(f'(assert ({leq} b{i} b{j}))')
            lines.append(f'(assert (=> (= b{i} b{j}) ({leq} a{i} a{j})))')
            lines.append(f'(assert (=> (and (= b{i} b{j}) (= a{i} a{j})) (or (not o{i}) o{j})))')
    if connected:
        for i in range(len(gates)-1):
            consumers = [f'(= {part}{j} {sel_lit(n+i)})'
                         for j in range(i+1, len(gates)) for part in ('a','b')]
            lines.append(f'(assert (or {" ".join(consumers)}))')
    if essential:
        for pin in range(n):
            uses = [f'(= {part}{i} {sel_lit(pin)})' for i in range(len(gates)) for part in ('a','b')]
            lines.append(f'(assert (or {" ".join(uses)}))')
    if first is not None:
        op, a, b = first
        a,b = sorted((a,b))
        lines.append(f'(assert (= o0 {str(bool(op)).lower()}))')
        lines.append(f'(assert (= a0 {sel_lit(a)}))')
        lines.append(f'(assert (= b0 {sel_lit(b)}))')
    if single_input is not None:
        bits = (2*len(gates)).bit_length()
        total = f'(_ bv0 {bits})'
        for i in range(len(gates)):
            for part in ('a','b'):
                use = f'(= {part}{i} {sel_lit(single_input)})'
                total = f'(bvadd {total} (ite {use} (_ bv1 {bits}) (_ bv0 {bits})))'
                if single_op is not None:
                    lines.append(f'(assert (=> {use} (= o{i} {str(single_op=="or").lower()})))')
        lines.append(f'(assert (= {total} (_ bv1 {bits})))')
    if single_or_helper:
        assert single_input==0 and single_op=='or'
        bad = sum(1 << (len(cases['positive'])+j)
                  for j,x in enumerate(cases['negative'])
                  if x & ~1 not in (200,772))
        j201 = len(cases['positive'])+cases['negative'].index(201)
        j773 = len(cases['positive'])+cases['negative'].index(773)
        for i in range(len(gates)):
            use = f'(or (= a{i} {sel_lit(0)}) (= b{i} {sel_lit(0)}))'
            helper = f'(ite (= a{i} {sel_lit(0)}) bv{i} av{i})'
            lines.append(f'(assert (=> {use} (= (bvand {helper} {lit(bad)}) {lit(0)})))')
            lines.append(f'(assert (=> {use} (or (= ((_ extract {j773} {j773}) {helper}) #b0) (= ((_ extract {j201} {j201}) {helper}) #b1))))')
    target = (1 << len(cases['positive'])) - 1
    lines.append(f'(assert (= v{n-1+len(gates)} {lit(target)}))')
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
    n = cases.get('inputs', 10)
    errors = []
    for x in range(1 << n):
        values = [(x >> i) & 1 for i in range(n)]
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
    ap.add_argument('--first', help='first gate op,a,b; op is and or or')
    ap.add_argument('--positive-live', action='store_true')
    ap.add_argument('--forbid-or', choices=('none','edges','all'), default='none')
    ap.add_argument('--single-input', type=int)
    ap.add_argument('--single-op', choices=('and','or'))
    ap.add_argument('--engine', choices=('generic','qfbv'), default='generic')
    ap.add_argument('--single-or-helper', action='store_true')
    ap.add_argument('--essential', action='store_true')
    ap.add_argument('--monotone-rows', action='store_true')
    args = ap.parse_args()
    cases = json.loads(args.cases.read_text())
    base = json.loads(args.base.read_text())
    gates = base['gates'] if isinstance(base, dict) else base
    free = {int(i) for i in args.free.split(',')} if args.free else None
    first = None
    if args.first:
        op,a,b = args.first.split(',')
        assert op in ('and','or')
        first = (int(op=='or'),int(a),int(b))
    args.out.mkdir(parents=True, exist_ok=True)
    smt = build_smt(cases, gates, args.edits, free, args.selector,
                    args.allow_repeat, args.canonical, args.connected,
                    first,args.positive_live,args.forbid_or,
                    args.single_input,args.single_op,args.single_or_helper,
                    args.essential,args.monotone_rows)
    (args.out/'problem.smt2').write_text(smt)
    z, ctx, solver = solver_api(args.timeout*1000, args.memory,args.engine)
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
              'canonical':args.canonical,'connected':args.connected,
              'first':first,'positive_live':args.positive_live,
              'forbid_or':args.forbid_or,'single_input':args.single_input,
              'single_op':args.single_op,'engine':args.engine}
    result['single_or_helper']=args.single_or_helper
    result['essential']=args.essential
    result['monotone_rows']=args.monotone_rows
    if status == 1:
        model = z.Z3_model_to_string(ctx, z.Z3_solver_get_model(ctx, solver)).decode()
        (args.out/'model.txt').write_text(model)
        candidate = parse_model(model, len(gates))
        errors = verify(cases, candidate)
        result.update(gates=candidate, exhaustive_errors=errors,
                      verified_assignments=1<<cases.get('inputs',10))
        if not errors:
            filename = 'WITNESS.json' if len(gates)<cases.get('baseline_size',20) else 'baseline-verified.json'
            (args.out/filename).write_text(json.dumps(result, indent=2)+'\n')
    elif status == 0:
        result['reason'] = z.Z3_solver_get_reason_unknown(ctx, solver).decode()
    (args.out/'result.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result), flush=True)
    z.Z3_solver_dec_ref(ctx, solver)
    z.Z3_del_context(ctx)


if __name__ == '__main__':
    main()
