import ctypes,ctypes.util,json,re,sys,time
from pathlib import Path
target=int(sys.argv[1],0);budget=int(sys.argv[2]);mode=sys.argv[3];prefix=Path(sys.argv[4]);timeout=int(sys.argv[5]) if len(sys.argv)>5 else 60000
assert mode in ['mono','one','atmost','full']
assert 0<target<2**32-1 and budget>0
n=5;width=32;base=7
idxwidth=(base+budget).bit_length();usedwidth=budget.bit_length()
def lit(v,bits):return f'(_ bv{v} {bits})'
def bv(v):return lit(v,width)
def idx(v):return lit(v,idxwidth)
def count(v):return lit(v,usedwidth)
def active(j):return f'(bvult {count(j)} used)'
variables=[sum(1<<x for x in range(width) if x>>v&1) for v in range(n)]
constants=variables+[0,(1<<width)-1]
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
if mode!='full':
    for i in range(budget):
        for j in range(i+1,budget):
            lines.append(f'(assert (or (distinct op{i} #b10) (distinct op{j} #b10)))')
if mode=='mono':
 for j in range(budget):lines.append(f'(assert (distinct op{j} #b10))')
if mode=='one':lines.append('(assert (or '+' '.join(f'(= op{j} #b10)' for j in range(budget))+'))')
lines.append(f'(assert (bvugt used {count(0)}))')
for j in range(budget):
 lines.append(f'(assert (=> (= used {count(j+1)}) (= g{j} {bv(target)})))')
 terms=[f'(= used {count(j+1)})']+[f'(and {active(k)} (= {name}{k} {idx(base+j)}))' for k in range(j+1,budget) for name in ['a','b']]
 lines.append(f'(assert (=> {active(j)} (or '+' '.join(terms)+')))')
for j in range(1,budget):
 i=j-1
 independent=f'(and (distinct a{j} {idx(base+i)}) (distinct b{j} {idx(base+i)}))'
 ordered=f'(or (bvult op{i} op{j}) (and (= op{i} op{j}) (or (bvult a{i} a{j}) (and (= a{i} a{j}) (bvule b{i} b{j})))))'
 lines.append(f'(assert (=> (and {active(j)} {independent}) {ordered}))')
lines.append('(check-sat-using qfbv)')
source='\n'.join(lines)+'\n';prefix.with_suffix('.smt2').write_text(source)
z=ctypes.CDLL(ctypes.util.find_library('z3'))
z.Z3_mk_config.restype=ctypes.c_void_p;z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p
z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
ctx=z.Z3_mk_context(z.Z3_mk_config());start=time.monotonic()
result=z.Z3_eval_smtlib2_string(ctx,source.encode()).decode().strip()
record={'target':hex(target),'budget':budget,'mode':mode,'result':result,'seconds':time.monotonic()-start}
print(json.dumps(record),flush=True)
prefix.with_suffix('.stats').write_text(z.Z3_eval_smtlib2_string(ctx,b'(get-info :all-statistics)').decode())
if result=='sat':
 query='(get-value (used '+' '.join(f'{name}{j}' for j in range(budget) for name in ['op','a','b'])+'))'
 model=z.Z3_eval_smtlib2_string(ctx,query.encode()).decode();prefix.with_suffix('.model').write_text(model)
 values={name:int(value[2:],16 if value[1]=='x' else 2) for name,value in re.findall(r'\((\w+) (#x[0-9a-fA-F]+|#b[01]+)\)',model)}
 used=values['used'];gates=[(values[f'op{j}'],values[f'a{j}'],values[f'b{j}']) for j in range(used)]
 vals=constants.copy()
 for op,a,b in gates:vals.append(vals[a]&vals[b] if op==0 else vals[a]|vals[b] if op==1 else vals[a]^((1<<width)-1))
 assert vals[-1]==target
 assert all(a not in [5,6] and b not in [5,6] for op,a,b in gates)
 actual=[{'op':['and','or','not'][op],'inputs':[a if a<5 else a-2]+([] if op==2 else [b if b<5 else b-2])} for op,a,b in gates]
 for x in range(32):
  w=[bool(x>>i&1) for i in range(5)]
  for g in actual:
   args=[w[j] if j<len(w) else False for j in g['inputs']]
   w.append(all(args) if g['op']=='and' else any(args) if g['op']=='or' else not args[0])
  assert w[-1]==bool(target>>x&1)
 record.update({'used':used,'gates_with_relaxed_indices':gates,'gates':actual,'output':5+used-1,'full_assignments_verified':32})
 print('VALID_FULL_CIRCUIT '+json.dumps(record),flush=True)
elif result=='unknown':record['reason']=z.Z3_eval_smtlib2_string(ctx,b'(get-info :reason-unknown)').decode();print(record['reason'],flush=True)
prefix.with_suffix('.result.json').write_text(json.dumps(record,indent=2)+'\n')
