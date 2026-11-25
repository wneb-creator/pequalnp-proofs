import ctypes
import ctypes.util
import sys
import time
from pathlib import Path

root=Path('/tmp/oec/pequalnp-pilot-138/semantic')
tests=[int(x) for x in (root/'constraints.txt').read_text().split()]
count=int(sys.argv[1]);seconds=int(sys.argv[2])
gs=[];stars=[]
for l in range(7):
    p=[l,(l+1)%7,(l+3)%7];n=14+len(gs)
    gs += [(p[0],p[1],False),(n,p[2],False),(n+1,7+l,True)];stars.append(n+2)
out=stars[0]
for star in stars[1:]:gs.append((out,star,False));out=13+len(gs)
if count==26:
    def rw(w):
        if w==15:w=14
        return w-1 if w>15 else w
    gs=[(rw(a),rw(b),op) for j,(a,b,op) in enumerate(gs) if j!=1]
assert len(gs)==count
preferred={};model=[]
signatures=[sum(1<<t for t,m in enumerate(tests) if m>>i&1) for i in range(14)]
for j,(a,b,op) in enumerate(gs):
    a,b=sorted([a,b]);n=14+j
    for i in range(n-1):preferred[f'a{j}_{i}']=i==a;model.append(f'a{j}_{i}')
    for i in range(1,n):preferred[f'b{j}_{i}']=i==b;model.append(f'b{j}_{i}')
    preferred[f'op{j}']=op;model.append(f'op{j}')
    val=signatures[a]&signatures[b] if op else signatures[a]|signatures[b]
    for t in range(58):
        preferred[f'x{j}_{t}']=bool(signatures[a]>>t&1)
        preferred[f'y{j}_{t}']=bool(signatures[b]>>t&1)
        preferred[f'v{j}_{t}']=bool(val>>t&1)
    signatures.append(val)
clauses=[]
def clause(*xs):clauses.append(xs)
def exactly_one(names):
    clause(*[(n,True) for n in names])
    for i,a in enumerate(names):
        for b in names[i+1:]:clause((a,False),(b,False))
for j in range(count):
    n=14+j;A=[f'a{j}_{i}' for i in range(n-1)];B=[f'b{j}_{i}' for i in range(1,n)]
    exactly_one(A);exactly_one(B)
    for i in range(1,n-1):
        for h in range(1,i+1):clause((f'a{j}_{i}',False),(f'b{j}_{h}',False))
    for t,m in enumerate(tests):
        for side,indices,value in [('a',range(n-1),f'x{j}_{t}'),('b',range(1,n),f'y{j}_{t}')]:
            for i in indices:
                sel=f'{side}{j}_{i}'
                if i<14:clause((sel,False),(value,bool(m>>i&1)))
                else:
                    v=f'v{i-14}_{t}'
                    clause((sel,False),(value,False),(v,True))
                    clause((sel,False),(value,True),(v,False))
        op=f'op{j}';x=f'x{j}_{t}';y=f'y{j}_{t}';v=f'v{j}_{t}'
        clause((op,False),(x,False),(y,False),(v,True))
        clause((op,False),(x,True),(v,False))
        clause((op,False),(y,True),(v,False))
        clause((op,True),(x,True),(y,True),(v,False))
        clause((op,True),(x,False),(v,True))
        clause((op,True),(y,False),(v,True))
for j in range(count-1):
    clause(*[(f'{side}{k}_{14+j}',True) for k in range(j+1,count) for side in ['a','b'] if side=='b' or j<k-1])
for t in range(58):clause((f'v{count-1}_{t}',t<21))
unsat=sum(not any(preferred[n]==v for n,v in c) for c in clauses)
assert unsat==(0 if count==27 else 1)
source=[f'(set-option :timeout {seconds*1000})','(set-option :produce-models true)',
        '(set-option :sat.phase always_false)','(set-option :sat.elim_vars false)']
for n,p in preferred.items():
    source.append(f'(declare-const raw_{n} Bool)')
    source.append(f'(define-fun {n} () Bool '+(f'(not raw_{n})' if p else f'raw_{n}')+')')
for c in clauses:
    lits=[n if p else f'(not {n})' for n,p in c]
    source.append('(assert '+(lits[0] if len(lits)==1 else '(or '+' '.join(lits)+')')+')')
source.append('(check-sat-using sat)')
script='\n'.join(source)+'\n'
(root/f'cnf-{count}-phase.smt2').write_text(script)
z3=ctypes.CDLL(ctypes.util.find_library('z3'))
z3.Z3_mk_config.restype=ctypes.c_void_p
z3.Z3_mk_context.argtypes=[ctypes.c_void_p];z3.Z3_mk_context.restype=ctypes.c_void_p
z3.Z3_del_config.argtypes=[ctypes.c_void_p];z3.Z3_del_context.argtypes=[ctypes.c_void_p]
z3.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z3.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
cfg=z3.Z3_mk_config();ctx=z3.Z3_mk_context(cfg);z3.Z3_del_config(cfg)
start=time.time();print(f'gates={count} tests=58 timeout_s={seconds} bytes={len(script)} clauses={len(clauses)} seed_unsatisfied_clauses={unsat}',flush=True)
output=z3.Z3_eval_smtlib2_string(ctx,script.encode()).decode();print(output,flush=True)
if output.strip()=='sat':print(z3.Z3_eval_smtlib2_string(ctx,('(get-value ('+' '.join(model)+'))').encode()).decode(),flush=True)
elif output.strip()=='unknown':print(z3.Z3_eval_smtlib2_string(ctx,b'(get-info :reason-unknown)').decode(),flush=True)
print(f'elapsed_s={time.time()-start:.3f}',flush=True);z3.Z3_del_context(ctx)
