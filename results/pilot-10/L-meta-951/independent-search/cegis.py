import ctypes
import ctypes.util
import json
import re
import sys
import time
from pathlib import Path

family=json.loads(sys.argv[1])
budget=int(sys.argv[2])
prefix=Path(sys.argv[3])
step_ms=int(sys.argv[4]) if len(sys.argv)>4 else 60000
tactic=sys.argv[5] if len(sys.argv)>5 else None
n=1+max(v for S in family for v in S)
assert all(len(set(S))>=2 for S in family)
assert all(len(set(S))==len(S) for S in family)
assert all(len(set(S)&set(T))<=1 for i,S in enumerate(family) for T in family[i+1:])
full=(1<<n)-1
rows=sorted({0,full}|{1<<v for v in range(n)}|{full^sum(1<<v for v in S) for S in family})
lib=ctypes.CDLL(ctypes.util.find_library('z3'))
lib.Z3_mk_config.restype=ctypes.c_void_p
lib.Z3_mk_context.argtypes=[ctypes.c_void_p]
lib.Z3_mk_context.restype=ctypes.c_void_p
lib.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p]
lib.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
lib.Z3_del_context.argtypes=[ctypes.c_void_p]
lib.Z3_del_config.argtypes=[ctypes.c_void_p]
start=time.monotonic()

for iteration in range(30):
    width=len(rows)
    def bv(v): return f'(_ bv{v} {width})'
    variables=[sum(1<<k for k,x in enumerate(rows) if (x>>v)&1) for v in range(n)]
    targets=[sum(1<<k for k,x in enumerate(rows) if any((x>>v)&1 for v in S)) for S in family]
    constants=variables+[0]
    lines=[f'(set-option :timeout {step_ms})','(set-option :produce-models true)','(declare-const used Int)',f'(assert (and (<= 0 used) (<= used {budget})))']
    for j in range(budget):
        wires=[bv(v) for v in constants]+[f'g{i}' for i in range(j)]
        for name in ['a','b','op']:
            lines.append(f'(declare-const {name}{j} Int)')
        lines.append(f'(declare-const g{j} (_ BitVec {width}))')
        lines.append(f'(assert (and (<= 0 a{j}) (< a{j} {len(wires)}) (<= 0 b{j}) (< b{j} {len(wires)}) (<= 0 op{j}) (<= op{j} 3)))')
        lines.append(f'(assert (ite (>= op{j} 2) (= a{j} b{j}) (<= a{j} b{j})))')
        lines.append(f'(assert (=> (= op{j} 3) (= a{j} 0)))')
        lines.append(f'(assert (=> (<= used {j}) (and (= op{j} 0) (= a{j} 0) (= b{j} 0))))')
        def choose(name):
            out=wires[-1]
            for k in reversed(range(len(wires)-1)):
                out=f'(ite (= {name}{j} {k}) {wires[k]} {out})'
            return out
        lines.append(f'(define-fun av{j} () (_ BitVec {width}) {choose("a")})')
        lines.append(f'(define-fun bv{j} () (_ BitVec {width}) {choose("b")})')
        lines.append(f'(assert (= g{j} (ite (= op{j} 0) (bvand av{j} bv{j}) (ite (= op{j} 1) (bvor av{j} bv{j}) (ite (= op{j} 2) (bvnot av{j}) {bv((1<<width)-1)})))))')
    lines.append('(assert (<= (+ '+' '.join(f'(ite (= op{j} 2) 1 0)' for j in range(budget))+') 1))')
    for k,target in enumerate(targets):
        lines.append(f'(declare-const out{k} Int)')
        lines.append(f'(assert (and (<= 0 out{k}) (< out{k} used)))')
        lines.append('(assert (or '+' '.join(f'(and (= out{k} {j}) (< {j} used) (= g{j} {bv(target)}))' for j in range(budget))+'))')
    for j in range(budget):
        terms=[f'(= out{k} {j})' for k in range(len(family))]+[f'(and (< {k} used) (= {name}{k} {n+1+j}))' for k in range(j+1,budget) for name in ['a','b']]
        lines.append(f'(assert (=> (< {j} used) (or '+' '.join(terms)+')))')
    lines.append(f'(check-sat-using {tactic})' if tactic else '(check-sat)')
    source='\n'.join(lines)+'\n'
    prefix.with_name(prefix.name+f'-{iteration:02d}.smt2').write_text(source)
    prefix.with_name(prefix.name+f'-{iteration:02d}.rows.json').write_text(json.dumps(rows)+'\n')
    config=lib.Z3_mk_config()
    context=lib.Z3_mk_context(config)
    result=lib.Z3_eval_smtlib2_string(context,source.encode()).decode().strip()
    print(json.dumps({'iteration':iteration,'rows':len(rows),'result':result,'seconds':time.monotonic()-start}),flush=True)
    if result!='sat':
        if result=='unknown':
            print(lib.Z3_eval_smtlib2_string(context,b'(get-info :reason-unknown)').decode(),flush=True)
        lib.Z3_del_context(context)
        lib.Z3_del_config(config)
        break
    query='(get-value (used '+' '.join(f'{name}{j}' for j in range(budget) for name in ['op','a','b'])+' '+' '.join(f'out{k}' for k in range(len(family)))+'))'
    model=lib.Z3_eval_smtlib2_string(context,query.encode()).decode()
    prefix.with_name(prefix.name+f'-{iteration:02d}.model').write_text(model)
    lib.Z3_del_context(context)
    lib.Z3_del_config(config)
    used=int(re.search(r'\(used (\d+)\)',model).group(1))
    values={(name,int(j)):int(v) for name,j,v in re.findall(r'\((op|a|b|out)(\d+) (\d+)\)',model)}
    gates=[(values['op',j],values['a',j],values['b',j]) for j in range(used)]
    outputs=[values['out',k] for k in range(len(family))]
    bad=[]
    for x in range(1<<n):
        wires=[bool((x>>v)&1) for v in range(n)]+[False]
        for op,a,b in gates:
            value=wires[a] and wires[b] if op==0 else wires[a] or wires[b] if op==1 else not wires[a] if op==2 else True
            wires.append(value)
        if any(wires[n+1+outputs[k]]!=any((x>>v)&1 for v in S) for k,S in enumerate(family)):
            assert x not in rows
            bad.append(x)
    print(json.dumps({'iteration':iteration,'used':used,'failing_full_assignments':len(bad)}),flush=True)
    if not bad:
        answer={'n':n,'family':family,'gates':gates,'outputs':outputs,'used':used,'bound':sum(len(S)-1 for S in family),'full_assignments_checked':1<<n,'actual_constant_true_is_counted':True}
        prefix.with_suffix('.witness.json').write_text(json.dumps(answer,indent=2)+'\n')
        print('VALID_FULL_CIRCUIT '+json.dumps(answer),flush=True)
        break
    # Spread refinements across the Boolean cube rather than only its prefix.
    additions={bad[0],bad[-1]}
    additions.update(bad[k*len(bad)//min(8,len(bad))] for k in range(min(8,len(bad))))
    rows=sorted(set(rows)|additions)
else:
    print('ITERATION_LIMIT',flush=True)
