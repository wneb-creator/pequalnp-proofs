import ctypes
import ctypes.util
import json
import re
import sys
import time
from pathlib import Path

edges=json.loads(sys.argv[1])
budget=int(sys.argv[2])
prefix=Path(sys.argv[3])
timeout=int(sys.argv[4]) if len(sys.argv)>4 else 600000
fixed=json.loads(Path(sys.argv[5]).read_text()) if len(sys.argv)>5 else None
n=1+max(v for e in edges for v in e)
assert all(len(e)==2 and e[0]<e[1] for e in edges)
assert len({tuple(e) for e in edges})==len(edges)
width=1<<n; base=n+2
idxwidth=(base+budget).bit_length(); usedwidth=budget.bit_length()
def lit(v,bits): return f'(_ bv{v} {bits})'
def bv(v): return lit(v,width)
def idx(v): return lit(v,idxwidth)
def count(v): return lit(v,usedwidth)
def active(j): return f'(bvult {count(j)} used)'
variables=[sum(1<<x for x in range(width) if (x>>v)&1) for v in range(n)]
constants=variables+[0,(1<<width)-1]
target=sum(1<<x for x in range(width) if any((x>>u)&1 and (x>>v)&1 for u,v in edges))
neighbors=[{v for a,b in edges for u,v in [(a,b),(b,a)] if u==w} for w in range(n)]
c4_free=all(len(neighbors[u]&neighbors[v])<2 for u in range(n) for v in range(u+1,n))
cover=min(x.bit_count() for x in range(width) if all((x>>u)&1 or (x>>v)&1 for u,v in edges))
lines=[f'(set-option :timeout {timeout})','(set-option :produce-models true)',f'(declare-const used (_ BitVec {usedwidth}))',f'(assert (and (bvugt used {count(0)}) (bvule used {count(budget)})))']
for j in range(budget):
    wires=[bv(v) for v in constants]+[f'g{i}' for i in range(j)]
    for name in ['a','b']: lines.append(f'(declare-const {name}{j} (_ BitVec {idxwidth}))')
    lines += [f'(declare-const op{j} (_ BitVec 1))',f'(declare-const g{j} (_ BitVec {width}))',f'(assert (and (bvule a{j} b{j}) (bvult b{j} {idx(len(wires))})))',f'(assert (=> (not {active(j)}) (and (= op{j} #b0) (= a{j} {idx(0)}) (= b{j} {idx(0)}))))']
    def choose(name):
        result=wires[-1]
        for k in reversed(range(len(wires)-1)): result=f'(ite (= {name}{j} {idx(k)}) {wires[k]} {result})'
        return result
    lines += [f'(define-fun av{j} () (_ BitVec {width}) {choose("a")})',f'(define-fun bv{j} () (_ BitVec {width}) {choose("b")})',f'(assert (= g{j} (ite (= op{j} #b0) (bvand av{j} bv{j}) (bvor av{j} bv{j}))))']
    for wire in wires: lines.append(f'(assert (=> {active(j)} (distinct g{j} {wire})))')
    lines.append(f'(assert (=> (= used {count(j+1)}) (= g{j} {bv(target)})))')
for j in range(1,budget):
    i=j-1
    independent=f'(and (distinct a{j} {idx(base+i)}) (distinct b{j} {idx(base+i)}))'
    ordered=f'(or (bvult op{i} op{j}) (and (= op{i} op{j}) (or (bvult a{i} a{j}) (and (= a{i} a{j}) (bvule b{i} b{j})))))'
    lines.append(f'(assert (=> (and {active(j)} {independent}) {ordered}))')
for j in range(budget):
    terms=[f'(= used {count(j+1)})']+[f'(and {active(k)} (= {name}{k} {idx(base+j)}))' for k in range(j+1,budget) for name in ['a','b']]
    lines.append(f'(assert (=> {active(j)} (or '+' '.join(terms)+')))')
if fixed is not None:
    assert len(fixed)<=budget
    lines.append(f'(assert (= used {count(len(fixed))}))')
    for j,(op,a,b) in enumerate(fixed): lines.append(f'(assert (and (= op{j} {lit(op,1)}) (= a{j} {idx(a)}) (= b{j} {idx(b)})))')
lines.append('(check-sat-using qfbv)')
source='\n'.join(lines)+'\n'; prefix.with_suffix('.smt2').write_text(source)
z=ctypes.CDLL(ctypes.util.find_library('z3'))
z.Z3_mk_config.restype=ctypes.c_void_p
z.Z3_mk_context.argtypes=[ctypes.c_void_p]; z.Z3_mk_context.restype=ctypes.c_void_p
z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p]; z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
c=z.Z3_mk_context(z.Z3_mk_config()); start=time.monotonic()
result=z.Z3_eval_smtlib2_string(c,source.encode()).decode().strip()
print(json.dumps({'n':n,'edges':edges,'edge_count':len(edges),'minimum_vertex_cover':cover,'C4_free':c4_free,'target_bound':len(edges)+cover-1,'budget':budget,'fixed_control':fixed is not None,'result':result,'seconds':time.monotonic()-start}),flush=True)
prefix.with_suffix('.stats').write_text(z.Z3_eval_smtlib2_string(c,b'(get-info :all-statistics)').decode())
if result=='sat':
    query='(get-value (used '+' '.join(f'{name}{j}' for j in range(budget) for name in ['op','a','b'])+'))'
    model=z.Z3_eval_smtlib2_string(c,query.encode()).decode(); prefix.with_suffix('.model').write_text(model)
    values={name:int(value[2:],16 if value[1]=='x' else 2) for name,value in re.findall(r'\((\w+) (#x[0-9a-fA-F]+|#b[01]+)\)',model)}
    used=values['used']; gates=[(values[f'op{j}'],values[f'a{j}'],values[f'b{j}']) for j in range(used)]
    for x in range(width):
        vals=[bool((x>>v)&1) for v in range(n)]+[False,True]
        for op,a,b in gates: vals.append(vals[a] and vals[b] if op==0 else vals[a] or vals[b])
        assert vals[-1]==any((x>>u)&1 and (x>>v)&1 for u,v in edges)
    answer={'n':n,'edges':edges,'gates':gates,'output_wire':base+used-1,'used':used,'free_constant_true_used':any(a==n+1 or b==n+1 for _,a,b in gates),'assignments_verified':width,'violates_target_bound':used<len(edges)+cover-1}
    prefix.with_suffix('.witness.json').write_text(json.dumps(answer,indent=2)+'\n')
    print('VALID_FULL_CIRCUIT '+json.dumps(answer),flush=True)
elif result=='unknown': print(z.Z3_eval_smtlib2_string(c,b'(get-info :reason-unknown)').decode(),flush=True)
