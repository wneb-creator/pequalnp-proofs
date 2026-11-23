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
exactly_one_not=len(sys.argv)>5 and sys.argv[5]=='one'
first_gate=json.loads(sys.argv[6]) if len(sys.argv)>6 else None
canonical_order=len(sys.argv)>7 and sys.argv[7]=='canonical'
constraint_mode=sys.argv[8] if len(sys.argv)>8 else None
n=1+max(v for S in family for v in S)
assert all(2<=len(S)==len(set(S)) for S in family)
assert all(len(set(S)&set(T))<=1 for i,S in enumerate(family) for T in family[i+1:])
width=1<<n
idxwidth=(n+2+budget).bit_length()
usedwidth=budget.bit_length()
def lit(v,bits): return f'(_ bv{v} {bits})'
def bv(v): return lit(v,width)
def idx(v): return lit(v,idxwidth)
def count(v): return lit(v,usedwidth)
def active(j): return f'(bvult {count(j)} used)'
variables=[sum(1<<x for x in range(width) if (x>>v)&1) for v in range(n)]
constants=variables+[0,(1<<width)-1]
targets=[sum(1<<x for x in range(width) if any((x>>v)&1 for v in S)) for S in family]
lines=[f'(set-option :timeout {timeout})','(set-option :produce-models true)',f'(declare-const used (_ BitVec {usedwidth}))',f'(assert (bvule used {count(budget)}))']
for j in range(budget):
    wires=[bv(v) for v in constants]+[f'g{i}' for i in range(j)]
    for name in ['a','b']:
        lines.append(f'(declare-const {name}{j} (_ BitVec {idxwidth}))')
    lines.append(f'(declare-const op{j} (_ BitVec 2))')
    lines.append(f'(declare-const g{j} (_ BitVec {width}))')
    lines.append(f'(assert (and (bvult a{j} {idx(len(wires))}) (bvult b{j} {idx(len(wires))}) (bvule op{j} #b10)))')
    lines.append(f'(assert (ite (= op{j} #b10) (= a{j} b{j}) (bvule a{j} b{j})))')
    lines.append(f'(assert (=> (not {active(j)}) (and (= op{j} #b00) (= a{j} {idx(0)}) (= b{j} {idx(0)}))))')
    def choose(name):
        result=wires[-1]
        for k in reversed(range(len(wires)-1)):
            result=f'(ite (= {name}{j} {idx(k)}) {wires[k]} {result})'
        return result
    lines.append(f'(define-fun av{j} () (_ BitVec {width}) {choose("a")})')
    lines.append(f'(define-fun bv{j} () (_ BitVec {width}) {choose("b")})')
    lines.append(f'(assert (= g{j} (ite (= op{j} #b00) (bvand av{j} bv{j}) (ite (= op{j} #b01) (bvor av{j} bv{j}) (bvnot av{j})))))')
    for wire in wires:
        lines.append(f'(assert (=> {active(j)} (distinct g{j} {wire})))')
for i in range(budget):
    for j in range(i+1,budget):
        lines.append(f'(assert (or (distinct op{i} #b10) (distinct op{j} #b10)))')
if exactly_one_not:
    lines.append('(assert (or '+' '.join(f'(= op{j} #b10)' for j in range(budget))+'))')
if first_gate is not None:
    op,a,b=first_gate
    lines.append(f'(assert (and (= op0 {lit(op,2)}) (= a0 {idx(a)}) (= b0 {idx(b)})))')
if canonical_order:
    # Hold gate zero fixed. Among later gates, choose a lexicographically
    # minimal topological ordering. Independent neighboring gates can be
    # swapped without changing their input indices or Boolean functions.
    for j in range(2,budget):
        i=j-1
        independent=f'(and (distinct a{j} {idx(len(constants)+i)}) (distinct b{j} {idx(len(constants)+i)}))'
        ordered=f'(or (bvult op{i} op{j}) (and (= op{i} op{j}) (or (bvult a{i} a{j}) (and (= a{i} a{j}) (bvule b{i} b{j})))))'
        lines.append(f'(assert (=> (and {active(j)} {independent}) {ordered}))')
for target in targets:
    lines.append('(assert (or '+' '.join(f'(and {active(j)} (= g{j} {bv(target)}))' for j in range(budget))+'))')
for j in range(budget):
    terms=[f'(= g{j} {bv(target)})' for target in targets]+[f'(and {active(k)} (= {name}{k} {idx(len(constants)+j)}))' for k in range(j+1,budget) for name in ['a','b']]
    lines.append(f'(assert (=> {active(j)} (or '+' '.join(terms)+')))')
if constraint_mode in ['tightgood','ownership','tightshape']:
    assert exactly_one_not
    if constraint_mode=='tightgood':
        assert budget==1+sum(min(len(S)-1,2) for S in family)
        lines.append(f'(assert (= used {lit(budget,usedwidth)}))')
    def bool_count(terms,bits):
        result=lit(0,bits)
        for term in terms:
            result=f'(bvadd {result} (ite {term} {lit(1,bits)} {lit(0,bits)}))'
        return result
    cw=max(usedwidth,(n+1).bit_length())
    for k,(S,target) in enumerate(zip(family,targets)):
        outside=((1<<n)-1)^sum(1<<v for v in S)
        for j in range(budget):
            hits=bool_count([f'(= ((_ extract {1<<v} {1<<v}) g{j}) #b1)' for v in S],cw)
            low=f'(= (bvand g{j} (bvnot {bv(target)})) {bv(0)})'
            high=f'(= (bvand {bv(target)} (bvnot g{j})) {bv(0)})'
            lines.append(f'(define-fun good_{k}_{j} () Bool (and {active(j)} (or {low} {high}) (bvuge {hits} {lit(2,cw)}) (= ((_ extract {outside} {outside}) g{j}) #b0)))')
        owned=bool_count([f'good_{k}_{j}' for j in range(budget)],usedwidth)
        comparator='=' if constraint_mode=='tightgood' else 'bvuge'
        lines.append(f'(assert ({comparator} {owned} {lit(min(len(S)-1,2),usedwidth)}))')
    for j in range(budget) if constraint_mode=='tightgood' else []:
        lines.append(f'(assert (or (= op{j} #b10) '+' '.join(f'good_{k}_{j}' for k in range(len(family)))+'))')
if constraint_mode=='tightshape':
    # Reviewed graph-bound equality conditions, not a kernel certificate.
    assert exactly_one_not
    lines.append(f'(assert (= used {lit(budget,usedwidth)}))')
    uses=[]
    for i in range(budget):
        for j in range(i+1,budget):
            for name in ['a','b']:
                uses.append(f'(and (= op{i} #b10) (distinct op{j} #b10) (= {name}{j} {idx(len(constants)+i)}))')
    edgewidth=(2*budget+1).bit_length()
    lines.append(f'(assert (= {bool_count(uses,edgewidth)} {lit(1,edgewidth)}))')
    for j in range(budget):
        terms=[f'(= g{j} {bv(target)})' for target in targets]
        terms += [f'(and (distinct op{k} #b10) (= {name}{k} {idx(len(constants)+j)}))' for k in range(j+1,budget) for name in ['a','b']]
        lines.append(f'(assert (=> (distinct op{j} #b10) (or '+ ' '.join(terms)+')))')
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
print(json.dumps({'n':n,'family':family,'budget':budget,'exactly_one_not':exactly_one_not,'first_gate':first_gate,'canonical_order':canonical_order,'constraint_mode':constraint_mode,'result':result,'seconds':time.monotonic()-start}),flush=True)
prefix.with_suffix('.stats').write_text(z.Z3_eval_smtlib2_string(c,b'(get-info :all-statistics)').decode())
if result=='sat':
    query='(get-value (used '+' '.join(f'{name}{j}' for j in range(budget) for name in ['op','a','b'])+'))'
    model=z.Z3_eval_smtlib2_string(c,query.encode()).decode()
    prefix.with_suffix('.model').write_text(model)
    pairs=re.findall(r'\((\w+) (#x[0-9a-fA-F]+|#b[01]+)\)',model)
    values={name:int(value[2:],16 if value[1]=='x' else 2) for name,value in pairs}
    used=values['used']
    gates=[(values[f'op{j}'],values[f'a{j}'],values[f'b{j}']) for j in range(used)]
    columns=[[] for _ in gates]
    for x in range(1<<n):
        vals=[bool((x>>v)&1) for v in range(n)]+[False,True]
        for j,(op,a,b) in enumerate(gates):
            value=vals[a] and vals[b] if op==0 else vals[a] or vals[b] if op==1 else not vals[a]
            vals.append(value)
            columns[j].append(value)
    outputs=[]
    for S in family:
        target=[any((x>>v)&1 for v in S) for x in range(1<<n)]
        outputs.append(columns.index(target))
    answer={'gates':gates,'outputs':outputs,'used':used,'free_constant_true_used':any(a==n+1 or b==n+1 for _,a,b in gates),'assignments_verified':1<<n}
    print('VALID_FULL_CIRCUIT '+json.dumps(answer),flush=True)
elif result=='unknown':
    print(z.Z3_eval_smtlib2_string(c,b'(get-info :reason-unknown)').decode(),flush=True)
