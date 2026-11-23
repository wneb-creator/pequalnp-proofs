import ctypes
import ctypes.util
import json
import sys
import time
from pathlib import Path

family = json.loads(sys.argv[1])
gate_count = int(sys.argv[2])
timeout_ms = int(sys.argv[3]) if len(sys.argv) > 3 else 120000
prefix = Path(sys.argv[4])
singleton_mode = len(sys.argv) > 5 and sys.argv[5] == 'singleton'
good_mode = len(sys.argv) > 5 and sys.argv[5] == 'good'
tactic = sys.argv[6] if len(sys.argv) > 6 else None
n = 1 + max(v for target in family for v in target)
if good_mode:
    n += 1
width = n if singleton_mode else 1 << n
variables = [1 << v for v in range(n)] if singleton_mode else [sum(1 << x for x in range(width) if (x >> v) & 1) for v in range(n)]
targets = [sum(1 << v for v in target) for target in family] if singleton_mode else [sum(1 << x for x in range(width) if any((x >> v) & 1 for v in target)) for target in family]
constants = variables + [0, (1 << width)-1]
assert all(len(set(t)) >= 2 for t in family)
assert all(len(set(t)) == len(t) for t in family)
assert all(len(set(a) & set(b)) <= 1 for i,a in enumerate(family) for b in family[i+1:])

def bv(v):
    return f'(_ bv{v} {width})'

lines = [f'(set-option :timeout {timeout_ms})', '(set-option :produce-models true)', '(declare-const used Int)', f'(assert (and (<= 0 used) (<= used {gate_count})))']
for j in range(gate_count):
    wires = [bv(c) for c in constants] + [f'g{i}' for i in range(j)]
    for name in ['a','b','op']:
        lines.append(f'(declare-const {name}{j} Int)')
    lines.append(f'(declare-const g{j} (_ BitVec {width}))')
    lines.append(f'(assert (and (<= 0 a{j}) (< a{j} {len(wires)}) (<= 0 b{j}) (< b{j} {len(wires)}) (<= 0 op{j}) (<= op{j} {1 if singleton_mode else 2})))')
    lines.append(f'(assert (ite (= op{j} 2) (= a{j} b{j}) (<= a{j} b{j})))')
    lines.append(f'(assert (=> (<= used {j}) (and (= op{j} 0) (= a{j} 0) (= b{j} 0))))')
    def choose(name):
        out = wires[-1]
        for i in reversed(range(len(wires)-1)):
            out = f'(ite (= {name}{j} {i}) {wires[i]} {out})'
        return out
    lines.append(f'(define-fun av{j} () (_ BitVec {width}) {choose("a")})')
    lines.append(f'(define-fun bv{j} () (_ BitVec {width}) {choose("b")})')
    lines.append(f'(assert (= g{j} (ite (= op{j} 0) (bvand av{j} bv{j}) (ite (= op{j} 1) (bvor av{j} bv{j}) (bvnot av{j})))))')
    for wire in wires:
        lines.append(f'(assert (=> (< {j} used) (distinct g{j} {wire})))')
lines.append('(assert (<= (+ ' + ' '.join(f'(ite (= op{j} 2) 1 0)' for j in range(gate_count)) + ') 1))')
for target in targets:
    lines.append('(assert (or ' + ' '.join(f'(and (< {j} used) (= g{j} {bv(target)}))' for j in range(gate_count)) + '))')
for j in range(gate_count):
    lines.append(f'(assert (=> (< {j} used) (or ' + ' '.join([f'(= g{j} {bv(target)})' for target in targets] + [f'(and (< {k} used) (= {name}{k} {len(constants)+j}))' for k in range(j+1,gate_count) for name in ['a','b']]) + ')))')
if good_mode:
    target=targets[0]
    outside=sum(1 << v for v in range(n) if v not in family[0])
    for j in range(gate_count):
        singleton_count='(+ ' + ' '.join(f'(ite (= ((_ extract {1 << v} {1 << v}) g{j}) #b1) 1 0)' for v in family[0]) + ')'
        lines.append(f'(define-fun good{j} () Bool (and (< {j} used) (or (= (bvand g{j} (bvnot {bv(target)})) {bv(0)}) (= (bvand {bv(target)} (bvnot g{j})) {bv(0)})) (>= {singleton_count} 2) (= ((_ extract {outside} {outside}) g{j}) #b0)))')
    lines.append('(assert (<= (+ ' + ' '.join(f'(ite good{j} 1 0)' for j in range(gate_count)) + f') {len(family[0])-2}))')
lines.append(f'(check-sat-using {tactic})' if tactic else '(check-sat)')
text='\n'.join(lines)+'\n'
prefix.with_suffix('.smt2').write_text(text)
lib=ctypes.CDLL(ctypes.util.find_library('z3'))
lib.Z3_mk_config.restype=ctypes.c_void_p
lib.Z3_mk_context.argtypes=[ctypes.c_void_p]
lib.Z3_mk_context.restype=ctypes.c_void_p
lib.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p]
lib.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
config=lib.Z3_mk_config()
context=lib.Z3_mk_context(config)
started=time.monotonic()
result=lib.Z3_eval_smtlib2_string(context,text.encode()).decode()
print(json.dumps({'n':n,'targets':family,'gate_count':gate_count,'singleton_mode':singleton_mode,'result':result.strip(),'seconds':time.monotonic()-started}),flush=True)
if result.strip()=='sat':
    query='(get-value (used ' + ' '.join(f'{name}{j}' for j in range(gate_count) for name in ['op','a','b','g']) + '))'
    print(lib.Z3_eval_smtlib2_string(context,query.encode()).decode(),flush=True)
