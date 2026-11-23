import ctypes
import ctypes.util
import json
import re
import sys
import time
from pathlib import Path

family=json.loads(sys.argv[1]); budget=int(sys.argv[2]); prefix=Path(sys.argv[3])
timeout=int(sys.argv[4]) if len(sys.argv)>4 else 120000
wall_limit=int(sys.argv[5]) if len(sys.argv)>5 else 600000
n=1+max(v for S in family for v in S); total=1<<n; base=n+3
assert all(2<=len(S)==len(set(S)) for S in family)
assert all(len(set(S)&set(T))<=1 for i,S in enumerate(family) for T in family[i+1:])
rows=sorted({0,total-1}|{1<<v for v in range(n)}|{(total-1)^sum(1<<v for v in S) for S in family})
iw=(base+budget).bit_length(); uw=budget.bit_length()
def lit(v,bits): return f'(_ bv{v} {bits})'
def idx(v): return lit(v,iw)
def active(j): return f'(bvult {lit(j,uw)} used)'
z=ctypes.CDLL(ctypes.util.find_library('z3'))
z.Z3_mk_config.restype=ctypes.c_void_p
z.Z3_mk_context.argtypes=[ctypes.c_void_p]; z.Z3_mk_context.restype=ctypes.c_void_p
z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p]; z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
z.Z3_del_context.argtypes=[ctypes.c_void_p]; z.Z3_del_config.argtypes=[ctypes.c_void_p]
started=time.monotonic()
for iteration in range(20):
    remaining=wall_limit-int(1000*(time.monotonic()-started))
    if remaining<=0:
        print('WALL_TIME_LIMIT',flush=True)
        break
    step_timeout=max(1,min(timeout,remaining))
    width=len(rows)
    def bv(v): return lit(v,width)
    variables=[sum(1<<k for k,x in enumerate(rows) if (x>>v)&1) for v in range(n)]
    targets=[sum(1<<k for k,x in enumerate(rows) if any((x>>v)&1 for v in S)) for S in family]
    inputs=[bv(v) for v in variables]+['u',bv(0),bv((1<<width)-1)]
    lines=[f'(set-option :timeout {step_timeout})','(set-option :produce-models true)',f'(declare-const used (_ BitVec {uw}))',f'(assert (bvule used {lit(budget,uw)}))',f'(declare-const u (_ BitVec {width}))']
    for i,x in enumerate(rows):
        for j,y in enumerate(rows):
            if i!=j and x&y==x:
                lines.append(f'(assert (=> (= ((_ extract {j} {j}) u) #b1) (= ((_ extract {i} {i}) u) #b1)))')
    for j in range(budget):
        wires=inputs+[f'g{i}' for i in range(j)]
        for name in ['a','b']: lines.append(f'(declare-const {name}{j} (_ BitVec {iw}))')
        lines += [f'(declare-const op{j} (_ BitVec 1))',f'(declare-const g{j} (_ BitVec {width}))',f'(assert (and (bvule a{j} b{j}) (bvult b{j} {idx(len(wires))})))',f'(assert (=> (not {active(j)}) (and (= op{j} #b0) (= a{j} {idx(0)}) (= b{j} {idx(0)}))))']
        def choose(name):
            result=wires[-1]
            for k in reversed(range(len(wires)-1)): result=f'(ite (= {name}{j} {idx(k)}) {wires[k]} {result})'
            return result
        lines += [f'(define-fun av{j} () (_ BitVec {width}) {choose("a")})',f'(define-fun bv{j} () (_ BitVec {width}) {choose("b")})',f'(assert (= g{j} (ite (= op{j} #b0) (bvand av{j} bv{j}) (bvor av{j} bv{j}))))']
    for j in range(1,budget):
        i=j-1
        independent=f'(and (distinct a{j} {idx(base+i)}) (distinct b{j} {idx(base+i)}))'
        ordered=f'(or (bvult op{i} op{j}) (and (= op{i} op{j}) (or (bvult a{i} a{j}) (and (= a{i} a{j}) (bvule b{i} b{j})))))'
        lines.append(f'(assert (=> (and {active(j)} {independent}) {ordered}))')
    for k,target in enumerate(targets):
        lines.append(f'(declare-const out{k} (_ BitVec {uw}))')
        lines.append(f'(assert (bvult out{k} used))')
        lines.append('(assert (or '+' '.join(f'(and (= out{k} {lit(j,uw)}) (= g{j} {bv(target)}))' for j in range(budget))+'))')
    for j in range(budget):
        terms=[f'(= out{k} {lit(j,uw)})' for k in range(len(family))]+[f'(and {active(k)} (= {name}{k} {idx(base+j)}))' for k in range(j+1,budget) for name in ['a','b']]
        lines.append(f'(assert (=> {active(j)} (or '+' '.join(terms)+')))')
    lines.append('(check-sat-using qfbv)')
    source='\n'.join(lines)+'\n'; run=prefix.with_name(prefix.name+f'-{iteration:02d}')
    run.with_suffix('.smt2').write_text(source); run.with_suffix('.rows.json').write_text(json.dumps(rows)+'\n')
    config=z.Z3_mk_config(); c=z.Z3_mk_context(config)
    result=z.Z3_eval_smtlib2_string(c,source.encode()).decode().strip()
    print(json.dumps({'iteration':iteration,'rows':len(rows),'result':result,'seconds':time.monotonic()-started}),flush=True)
    run.with_suffix('.stats').write_text(z.Z3_eval_smtlib2_string(c,b'(get-info :all-statistics)').decode())
    if result!='sat':
        if result=='unknown': print(z.Z3_eval_smtlib2_string(c,b'(get-info :reason-unknown)').decode(),flush=True)
        z.Z3_del_context(c); z.Z3_del_config(config); break
    query='(get-value (used '+' '.join(f'{name}{j}' for j in range(budget) for name in ['op','a','b'])+' '+' '.join(f'out{k}' for k in range(len(family)))+'))'
    model=z.Z3_eval_smtlib2_string(c,query.encode()).decode(); run.with_suffix('.model').write_text(model)
    z.Z3_del_context(c); z.Z3_del_config(config)
    pairs=re.findall(r'\((\w+) (#x[0-9a-fA-F]+|#b[01]+)\)',model)
    values={name:int(value[2:],16 if value[1]=='x' else 2) for name,value in pairs}; used=values['used']
    gates=[(values[f'op{j}'],values[f'a{j}'],values[f'b{j}']) for j in range(used)]; outputs=[values[f'out{k}'] for k in range(len(family))]
    allowed=[]
    for x in range(total):
        ok=[]
        for oracle in [False,True]:
            vals=[bool((x>>v)&1) for v in range(n)]+[oracle,False,True]
            for op,a,b in gates: vals.append(vals[a] and vals[b] if op==0 else vals[a] or vals[b])
            ok.append(all(vals[base+outputs[k]]==any((x>>v)&1 for v in S) for k,S in enumerate(family)))
        allowed.append(ok)
    bad=[x for x,ok in enumerate(allowed) if not any(ok)]
    forced_one=[not ok[0] and ok[1] for ok in allowed]; closure=forced_one.copy()
    for v in range(n):
        for x in range(total):
            if not (x>>v)&1: closure[x]=closure[x] or closure[x|(1<<v)]
    conflicts=[x for x,ok in enumerate(allowed) if ok[0] and not ok[1] and closure[x]]
    print(json.dumps({'iteration':iteration,'used':used,'invalid_assignments':len(bad),'antitone_conflicts':len(conflicts)}),flush=True)
    if not bad and not conflicts:
        assert all(allowed[x][int(closure[x])] for x in range(total))
        assert all(not closure[x|(1<<v)] or closure[x] for x in range(total) for v in range(n) if not (x>>v)&1)
        answer={'n':n,'family':family,'gates':gates,'outputs':outputs,'used':used,'oracle_truth_table_hex':hex(sum(1<<x for x,value in enumerate(closure) if value)),'full_assignments_verified':total,'relaxed_model_only':True,'violates_sum_bound':used<sum(len(S)-1 for S in family)}
        prefix.with_suffix('.witness.json').write_text(json.dumps(answer,indent=2)+'\n'); print('VALID_RELAXED_CIRCUIT '+json.dumps(answer),flush=True); break
    additions=set(bad[k*len(bad)//min(8,len(bad))] for k in range(min(8,len(bad))))
    for x in conflicts[:4]:
        y=next(y for y in range(total) if forced_one[y] and x&y==x)
        additions.update([x,y])
    assert additions-set(rows)
    rows=sorted(set(rows)|additions)
else:
    print('ITERATION_LIMIT',flush=True)
