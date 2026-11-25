import argparse,ctypes,ctypes.util,json,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=6);p.add_argument('--gates',type=int,default=8);p.add_argument('--junk',type=int,default=1);p.add_argument('--timeout',type=int,default=60000);p.add_argument('--edges',default='');a=p.parse_args()
n=a.n;k=a.gates;w=1<<n;mask=(1<<w)-1
edges=[tuple(map(int,e.split('-'))) for e in a.edges.split(',')] if a.edges else [(i,(i+1)%n) for i in range(n)]
ins=[sum(1<<v for v in range(w) if (v>>j)&1) for j in range(n)]
f=sum(1<<v for v in range(w) if any((v>>u)&1 and (v>>z)&1 for u,z in edges))
def bv(x):return f'(_ bv{x} {w})'
def selected(choices,sel):
    out=choices[-1]
    for j in reversed(range(len(choices)-1)):out=f'(ite (= {sel} {j}) {choices[j]} {out})'
    return out
lines=['(set-option :produce-models true)',f'(set-option :timeout {a.timeout})','(set-logic QF_AUFBV)']
# Use bitvectors for selectors, avoiding the integer arithmetic theory.
selw=max(1,(n+k-1).bit_length())
for j,x in enumerate(ins):lines.append(f'(define-fun x{j} () (_ BitVec {w}) {bv(x)})')
for i in range(k):
    vs=[f'x{j}' for j in range(n)]+[f'v{j}' for j in range(i)]
    for var in ['a','b']:lines.append(f'(declare-fun {var}{i} () (_ BitVec {selw}))')
    lines.append(f'(declare-fun op{i} () Bool)')
    lines.append(f'(assert (bvult a{i} b{i}))')
    lines.append(f'(assert (bvult b{i} (_ bv{n+i} {selw})))')
    def choose(sel):
        out=vs[-1]
        for j in reversed(range(len(vs)-1)):out=f'(ite (= {sel} (_ bv{j} {selw})) {vs[j]} {out})'
        return out
    lines.append(f'(define-fun la{i} () (_ BitVec {w}) {choose(f"a{i}")})')
    lines.append(f'(define-fun lb{i} () (_ BitVec {w}) {choose(f"b{i}")})')
    lines.append(f'(define-fun v{i} () (_ BitVec {w}) (ite op{i} (bvand la{i} lb{i}) (bvor la{i} lb{i})))')
    lines.append(f'(define-fun junk{i} () Bool (and op{i} (distinct (bvand v{i} {bv(mask^f)}) {bv(0)})))')
    for j in range(i):lines.append(f'(assert (distinct v{i} v{j}))')
    for j in range(n):lines.append(f'(assert (distinct v{i} x{j}))')
    if i>0:
        # An independent pair of consecutive gates can be sorted by argument pair/op.
        lines.append(f'(assert (or (= a{i} (_ bv{n+i-1} {selw})) (= b{i} (_ bv{n+i-1} {selw})) (bvule b{i-1} b{i})))')
lines.append(f'(assert (= v{k-1} {bv(f)}))')
if a.junk>=0:
    countw=max(1,(k+1).bit_length())
    ss=[f'(ite junk{i} (_ bv1 {countw}) (_ bv0 {countw}))' for i in range(k)]
    sm=ss[0]
    for s in ss[1:]:sm=f'(bvadd {sm} {s})'
    lines.append(f'(assert (= {sm} (_ bv{a.junk} {countw})))')
for i in range(k-1):
    readers=[f'(= {v}{j} (_ bv{n+i} {selw}))' for j in range(i+1,k) for v in ['a','b']]
    lines.append('(assert (or '+' '.join(readers)+'))')
if not a.edges:
    lines.append(f'(assert (= a0 (_ bv0 {selw})))')
    lines.append(f'(assert (bvule b0 (_ bv{n//2} {selw})))')
lines.append('(check-sat)')
model_command='(get-value ('+' '.join(f'a{i} b{i} op{i} junk{i}' for i in range(k))+'))'
script='\n'.join(lines)
path=Path('/tmp/oec/pequalnp-pilot-176')/f'antecedent-n{n}-k{k}-j{a.junk}.smt2';path.write_text(script)
z=ctypes.CDLL(ctypes.util.find_library('z3'))
z.Z3_mk_config.restype=ctypes.c_void_p;z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p
z.Z3_del_config.argtypes=[ctypes.c_void_p];z.Z3_del_context.argtypes=[ctypes.c_void_p]
z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
conf=z.Z3_mk_config();ctx=z.Z3_mk_context(conf);z.Z3_del_config(conf)
print(json.dumps({'n':n,'gates':k,'junk':a.junk,'edges':edges}),flush=True)
t=time.time();out=z.Z3_eval_smtlib2_string(ctx,script.encode()).decode();print(out,flush=True);print('elapsed',time.time()-t,flush=True)
if out.strip()=='sat': print(z.Z3_eval_smtlib2_string(ctx,model_command.encode()).decode(),flush=True)
z.Z3_del_context(ctx)
