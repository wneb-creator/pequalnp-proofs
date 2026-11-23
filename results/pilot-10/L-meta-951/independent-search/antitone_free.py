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
base=n+3
iw=(base+budget).bit_length()
uw=budget.bit_length()
def lit(v,bits): return f'(_ bv{v} {bits})'
def bv(v): return lit(v,width)
def idx(v): return lit(v,iw)
def active(j): return f'(bvult {lit(j,uw)} used)'
variables=[sum(1<<x for x in range(width) if (x>>v)&1) for v in range(n)]
targets=[sum(1<<x for x in range(width) if any((x>>v)&1 for v in S)) for S in family]
inputs=[bv(v) for v in variables]+['u',bv(0),bv((1<<width)-1)]
lines=[f'(set-option :timeout {timeout})','(set-option :produce-models true)',f'(declare-const used (_ BitVec {uw}))',f'(assert (bvule used {lit(budget,uw)}))',f'(declare-const u (_ BitVec {width}))']
for x in range(width):
    for v in range(n):
        if not ((x>>v)&1):
            y=x|(1<<v)
            lines.append(f'(assert (=> (= ((_ extract {y} {y}) u) #b1) (= ((_ extract {x} {x}) u) #b1)))')
for j in range(budget):
    wires=inputs+[f'g{i}' for i in range(j)]
    for name in ['a','b']:
        lines.append(f'(declare-const {name}{j} (_ BitVec {iw}))')
    lines.append(f'(declare-const op{j} (_ BitVec 1))')
    lines.append(f'(declare-const g{j} (_ BitVec {width}))')
    lines.append(f'(assert (and (bvule a{j} b{j}) (bvult b{j} {idx(len(wires))})))')
    lines.append(f'(assert (=> (not {active(j)}) (and (= op{j} #b0) (= a{j} {idx(0)}) (= b{j} {idx(0)}))))')
    def choose(name):
        result=wires[-1]
        for k in reversed(range(len(wires)-1)):
            result=f'(ite (= {name}{j} {idx(k)}) {wires[k]} {result})'
        return result
    lines.append(f'(define-fun av{j} () (_ BitVec {width}) {choose("a")})')
    lines.append(f'(define-fun bv{j} () (_ BitVec {width}) {choose("b")})')
    lines.append(f'(assert (= g{j} (ite (= op{j} #b0) (bvand av{j} bv{j}) (bvor av{j} bv{j}))))')
    for wire in wires:
        lines.append(f'(assert (=> {active(j)} (distinct g{j} {wire})))')
for j in range(1,budget):
    i=j-1
    independent=f'(and (distinct a{j} {idx(base+i)}) (distinct b{j} {idx(base+i)}))'
    ordered=f'(or (bvult op{i} op{j}) (and (= op{i} op{j}) (or (bvult a{i} a{j}) (and (= a{i} a{j}) (bvule b{i} b{j})))))'
    lines.append(f'(assert (=> (and {active(j)} {independent}) {ordered}))')
for target in targets:
    lines.append('(assert (or '+' '.join(f'(and {active(j)} (= g{j} {bv(target)}))' for j in range(budget))+'))')
for j in range(budget):
    terms=[f'(= g{j} {bv(target)})' for target in targets]+[f'(and {active(k)} (= {name}{k} {idx(base+j)}))' for k in range(j+1,budget) for name in ['a','b']]
    lines.append(f'(assert (=> {active(j)} (or '+' '.join(terms)+')))')
lines.append('(check-sat-using qfbv)')
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
print(json.dumps({'n':n,'family':family,'budget':budget,'free_antitone_input':True,'result':result,'seconds':time.monotonic()-start}),flush=True)
prefix.with_suffix('.stats').write_text(z.Z3_eval_smtlib2_string(c,b'(get-info :all-statistics)').decode())
if result=='sat':
    query='(get-value (used u '+' '.join(f'{name}{j}' for j in range(budget) for name in ['op','a','b'])+'))'
    model=z.Z3_eval_smtlib2_string(c,query.encode()).decode()
    prefix.with_suffix('.model').write_text(model)
    pairs=re.findall(r'\((\w+) (#x[0-9a-fA-F]+|#b[01]+)\)',model)
    values={name:int(value[2:],16 if value[1]=='x' else 2) for name,value in pairs}
    used=values['used']
    u=values['u']
    assert all(not ((u>>(x|(1<<v)))&1) or ((u>>x)&1) for x in range(width) for v in range(n) if not ((x>>v)&1))
    gates=[(values[f'op{j}'],values[f'a{j}'],values[f'b{j}']) for j in range(used)]
    columns=[[] for _ in gates]
    for x in range(width):
        vals=[bool((x>>v)&1) for v in range(n)]+[bool((u>>x)&1),False,True]
        for j,(op,a,b) in enumerate(gates):
            value=vals[a] and vals[b] if op==0 else vals[a] or vals[b]
            vals.append(value)
            columns[j].append(value)
    outputs=[]
    for S in family:
        target=[any((x>>v)&1 for v in S) for x in range(width)]
        outputs.append(columns.index(target))
    answer={'gates':gates,'outputs':outputs,'used':used,'free_antitone_truth_table_hex':hex(u),'assignments_verified':width,'relaxed_model_only':True,'violates_sum_bound':used<sum(len(S)-1 for S in family),'oracle_is_used':any(a==n or b==n for _,a,b in gates)}
    print('VALID_RELAXED_CIRCUIT '+json.dumps(answer),flush=True)
elif result=='unknown':
    print(z.Z3_eval_smtlib2_string(c,b'(get-info :reason-unknown)').decode(),flush=True)
