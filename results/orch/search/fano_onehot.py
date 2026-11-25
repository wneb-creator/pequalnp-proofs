import ctypes
import ctypes.util
import sys
import time
from pathlib import Path

root = Path('/tmp/oec/pequalnp-pilot-138/semantic')
tests = [int(x) for x in (root / 'constraints.txt').read_text().split()]
count = int(sys.argv[1]) if len(sys.argv) > 1 else 26
seconds = int(sys.argv[2]) if len(sys.argv) > 2 else 300
fixed = len(sys.argv)>3 and sys.argv[3]=='fixed'
anchor = len(sys.argv)>3 and sys.argv[3]=='anchor'
phase = len(sys.argv)>3 and sys.argv[3]=='phase'
job = f'onehot-{count}' + ('-fixed' if fixed else '-anchor' if anchor else '-phase' if phase else '')
source = [f'(set-option :timeout {seconds*1000})', '(set-option :produce-models true)',
          '(set-option :sat.random_seed 138)']
preferred={}
if phase:
    source.append('(set-option :sat.phase always_false)')
    gs=[];stars=[]
    for l in range(7):
        p=[l,(l+1)%7,(l+3)%7];n=14+len(gs)
        gs += [(p[0],p[1],False),(n,p[2],False),(n+1,7+l,True)]
        stars.append(n+2)
    out=stars[0]
    for star in stars[1:]:gs.append((out,star,False));out=13+len(gs)
    if count==26:
        def rw(w):
            if w==15:w=14
            return w-1 if w>15 else w
        gs=[(rw(a),rw(b),op) for j,(a,b,op) in enumerate(gs) if j!=1]
    assert len(gs)==count
    signatures=[sum(1<<t for t,m in enumerate(tests) if m>>i&1) for i in range(14)]
    for j,(a,b,op) in enumerate(gs):
        a,b=sorted([a,b]);n=14+j
        for i in range(n-1):preferred[f'a{j}_{i}']=i==a
        for i in range(1,n):preferred[f'b{j}_{i}']=i==b
        preferred[f'op{j}']=op
        val=signatures[a]&signatures[b] if op else signatures[a]|signatures[b]
        signatures.append(val)
        for t in range(58):preferred[f'v{j}_{t}']=bool(val>>t&1)
def disj(xs):
    if not xs:return 'false'
    if len(xs)==1:return xs[0]
    return '(or '+' '.join(xs)+')'
def declare(name):
    if phase:
        source.append(f'(declare-const raw_{name} Bool)')
        source.append(f'(define-fun {name} () Bool '+(f'(not raw_{name})' if preferred[name] else f'raw_{name}')+')')
    else:
        source.append(f'(declare-const {name} Bool)')
def exactly_one(names):
    source.append('(assert '+disj(names)+')')
    for i,a in enumerate(names):
        for b in names[i+1:]:source.append(f'(assert (or (not {a}) (not {b})))')
def wire(i,t):
    if i<14:return 'true' if tests[t]>>i&1 else 'false'
    return f'v{i-14}_{t}'
modelvars=[]
for j in range(count):
    n=14+j
    A=[f'a{j}_{i}' for i in range(n-1)]
    B=[f'b{j}_{i}' for i in range(1,n)]
    for name in A+B+[f'op{j}']:declare(name)
    modelvars+=A+B+[f'op{j}']
    exactly_one(A);exactly_one(B)
    for i in range(1,n-1):
        for h in range(1,i+1):source.append(f'(assert (or (not a{j}_{i}) (not b{j}_{h})))')
    for t in range(58):
        xs=[f'a{j}_{i}' if wire(i,t)=='true' else f'(and a{j}_{i} {wire(i,t)})' for i in range(n-1) if wire(i,t)!='false']
        ys=[f'b{j}_{i}' if wire(i,t)=='true' else f'(and b{j}_{i} {wire(i,t)})' for i in range(1,n) if wire(i,t)!='false']
        source.append(f'(define-fun x{j}_{t} () Bool {disj(xs)})')
        source.append(f'(define-fun y{j}_{t} () Bool {disj(ys)})')
        declare(f'v{j}_{t}')
        source.append(f'(assert (= v{j}_{t} (ite op{j} (and x{j}_{t} y{j}_{t}) (or x{j}_{t} y{j}_{t}))))')
    source.append('(assert '+disj([f'(not (= v{j}_{t} x{j}_{t}))' for t in range(58)])+')')
    source.append('(assert '+disj([f'(not (= v{j}_{t} y{j}_{t}))' for t in range(58)])+')')
for j in range(count-1):
    source.append('(assert '+disj([f'{side}{k}_{14+j}' for k in range(j+1,count) for side in ['a','b'] if side=='b' or j<k-1])+')')
for t in range(58):source.append(f'(assert {"v"+str(count-1)+"_"+str(t) if t<21 else "(not v"+str(count-1)+"_"+str(t)+")"})')
if anchor:
    source+=['(assert a0_0)','(assert b0_1)','(assert (not op0))']
if fixed:
    gs=[];stars=[]
    for l in range(7):
        p=[l,(l+1)%7,(l+3)%7];n=14+len(gs)
        gs += [(p[0],p[1],False),(n,p[2],False),(n+1,7+l,True)]
        stars.append(n+2)
    out=stars[0]
    for star in stars[1:]:gs.append((out,star,False));out=13+len(gs)
    assert len(gs)==count
    for j,(a,b,op) in enumerate(gs):
        a,b=sorted([a,b]);source += [f'(assert a{j}_{a})',f'(assert b{j}_{b})',f'(assert (= op{j} {str(op).lower()}))']
source.append('(check-sat-using sat)')
script='\n'.join(source)+'\n'
(root/(job+'.smt2')).write_text(script)
z3=ctypes.CDLL(ctypes.util.find_library('z3'))
z3.Z3_mk_config.restype=ctypes.c_void_p
z3.Z3_mk_context.argtypes=[ctypes.c_void_p];z3.Z3_mk_context.restype=ctypes.c_void_p
z3.Z3_del_config.argtypes=[ctypes.c_void_p];z3.Z3_del_context.argtypes=[ctypes.c_void_p]
z3.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z3.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
cfg=z3.Z3_mk_config();ctx=z3.Z3_mk_context(cfg);z3.Z3_del_config(cfg)
start=time.time();print(f'gates={count} tests=58 timeout_s={seconds} bytes={len(script)}',flush=True)
output=z3.Z3_eval_smtlib2_string(ctx,script.encode()).decode();print(output,flush=True)
if output.strip()=='sat':
    query='(get-value ('+' '.join(modelvars)+'))'
    print(z3.Z3_eval_smtlib2_string(ctx,query.encode()).decode(),flush=True)
elif output.strip()=='unknown':
    print(z3.Z3_eval_smtlib2_string(ctx,b'(get-info :reason-unknown)').decode(),flush=True)
print(f'elapsed_s={time.time()-start:.3f}',flush=True)
z3.Z3_del_context(ctx)
