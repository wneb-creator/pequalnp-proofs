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
timeout=int(sys.argv[4]) if len(sys.argv)>4 else 120000
n=1+max(v for S in family for v in S)
assert all(2<=len(S)==len(set(S)) for S in family)
assert all(len(set(S)&set(T))<=1 for i,S in enumerate(family) for T in family[i+1:])
width=1<<n
def bv(v): return f'(_ bv{v} {width})'
variables=[sum(1<<x for x in range(width) if (x>>v)&1) for v in range(n)]
constants=variables+[0,(1<<width)-1]
targets=[sum(1<<x for x in range(width) if any((x>>v)&1 for v in S)) for S in family]
lines=[f'(set-option :timeout {timeout})','(set-option :produce-models true)','(declare-const used Int)',f'(assert (and (<= 0 used) (<= used {budget})))']
for j in range(budget):
    wires=[bv(v) for v in constants]+[f'g{i}' for i in range(j)]
    for name in ['a','b','op']:
        lines.append(f'(declare-const {name}{j} Int)')
    lines.append(f'(declare-const g{j} (_ BitVec {width}))')
    lines.append(f'(assert (and (<= 0 a{j}) (<= a{j} b{j}) (< b{j} {len(wires)}) (<= 0 op{j}) (<= op{j} 1)))')
    lines.append(f'(assert (=> (<= used {j}) (and (= op{j} 0) (= a{j} 0) (= b{j} 0))))')
    def choose(name):
        result=wires[-1]
        for k in reversed(range(len(wires)-1)):
            result=f'(ite (= {name}{j} {k}) {wires[k]} {result})'
        return result
    lines.append(f'(define-fun av{j} () (_ BitVec {width}) {choose("a")})')
    lines.append(f'(define-fun bv{j} () (_ BitVec {width}) {choose("b")})')
    lines.append(f'(assert (= g{j} (ite (= op{j} 0) (bvand av{j} bv{j}) (bvor av{j} bv{j}))))')
    for wire in wires:
        lines.append(f'(assert (=> (< {j} used) (distinct g{j} {wire})))')
wires=[bv(v) for v in constants]+[f'g{i}' for i in range(budget)]
lines+=['(declare-const hi Int)',f'(assert (and (<= 0 hi) (< hi (+ {len(constants)} used))))',f'(declare-const h (_ BitVec {width}))']
lines.append('(assert (or '+' '.join(f'(and (= hi {j}) (= h {v}))' for j,v in enumerate(wires))+'))')
for k,(S,target) in enumerate(zip(family,targets)):
    outside=((1<<n)-1)^sum(1<<v for v in S)
    lines.append(f'(assert (= ((_ extract {outside} {outside}) h) #b1))')
    lines.append(f'(declare-const out{k} Int)')
    lines.append(f'(assert (and (<= 0 out{k}) (< out{k} used)))')
    terms=[f'(and (= out{k} {j}) (< {j} used) (= (bvand g{j} (bvnot {bv(target)})) {bv(0)}) (= (bvand (bvand h {bv(target)}) (bvnot g{j})) {bv(0)}))' for j in range(budget)]
    lines.append('(assert (or '+' '.join(terms)+'))')
for j in range(budget):
    terms=[f'(= hi {len(constants)+j})']+[f'(= out{k} {j})' for k in range(len(family))]+[f'(and (< {k} used) (= {name}{k} {len(constants)+j}))' for k in range(j+1,budget) for name in ['a','b']]
    lines.append(f'(assert (=> (< {j} used) (or '+' '.join(terms)+')))')
lines.append('(check-sat)')
source='\n'.join(lines)+'\n'
prefix.with_suffix('.smt2').write_text(source)
z=ctypes.CDLL(ctypes.util.find_library('z3'))
z.Z3_mk_config.restype=ctypes.c_void_p
z.Z3_mk_context.argtypes=[ctypes.c_void_p]
z.Z3_mk_context.restype=ctypes.c_void_p
z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p]
z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
c=z.Z3_mk_context(z.Z3_mk_config())
start=time.monotonic()
result=z.Z3_eval_smtlib2_string(c,source.encode()).decode().strip()
print(json.dumps({'n':n,'family':family,'budget':budget,'result':result,'seconds':time.monotonic()-start}),flush=True)
if result=='sat':
    query='(get-value (used hi '+' '.join(f'{name}{j}' for j in range(budget) for name in ['op','a','b'])+' '+' '.join(f'out{k}' for k in range(len(family)))+'))'
    model=z.Z3_eval_smtlib2_string(c,query.encode()).decode()
    prefix.with_suffix('.model').write_text(model)
    used=int(re.search(r'\(used (\d+)\)',model).group(1))
    hi=int(re.search(r'\(hi (\d+)\)',model).group(1))
    vs={(name,int(j)):int(v) for name,j,v in re.findall(r'\((op|a|b|out)(\d+) (\d+)\)',model)}
    gates=[(vs['op',j],vs['a',j],vs['b',j]) for j in range(used)]
    outputs=[vs['out',k] for k in range(len(family))]
    allrows=[]
    for x in range(1<<n):
        vals=[bool((x>>v)&1) for v in range(n)]+[False,True]
        for op,a,b in gates:
            vals.append(vals[a] and vals[b] if op==0 else vals[a] or vals[b])
        for k,S in enumerate(family):
            target=any((x>>v)&1 for v in S)
            out=vals[len(constants)+outputs[k]]
            assert not out or target
            assert not (vals[hi] and target) or out
        allrows.append(vals)
    assert all(allrows[((1<<n)-1)^sum(1<<v for v in S)][hi] for S in family)
    answer={'gates':gates,'hi':hi,'outputs':outputs,'used':used,'free_constant_true_used':hi==n+1 or any(a==n+1 or b==n+1 for _,a,b in gates),'assignments_verified':1<<n}
    print('VALID_CONDITIONAL '+json.dumps(answer),flush=True)
