import argparse, ctypes, json, time
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--bypasses',type=int,default=1);ap.add_argument('--radius',type=int,required=True);ap.add_argument('--limit',type=int,default=120);ap.add_argument('--seed',type=int,default=0);ap.add_argument('--out',required=True);a=ap.parse_args()
p=l=7;n=14;E=[(i,j) for i in range(7) for j in range(7) if (i-j)%7 in [0,1,3]]
def is_true(x):return any((x>>u&1) and (x>>(p+v)&1) for u,v in E)
rows=[(1<<u)|(1<<(p+v)) for u,v in E]+[x for x in range(1<<n) if not is_true(x) and all((x>>i&1) or is_true(x|(1<<i)) for i in range(n))]
W=len(rows);seed=[];terms=[]
def gate(op,u,v):
 seed.append((op,min(u,v),max(u,v)));return n+len(seed)-1
for u in range(p):
 ys=[p+v for v in range(l) if (u-v)%7 in [0,1,3]]
 terms.append(gate(False,u,gate(True,gate(True,ys[0],ys[1]),ys[2])))
while len(terms)>1:terms.append(gate(True,terms.pop(0),terms.pop(0)))
k=len(seed);B=(n+k).bit_length();C=k.bit_length()
def bv(x,w):return f'(_ bv{x} {w})'
def fold(op,xs,default):
 if not xs:return default
 if len(xs)==1:return xs[0]
 return '('+op+' '+' '.join(xs)+')'
def select(sel,kind,m):
 ans=kind+str(m-1)
 for i in range(m-2,-1,-1):ans=f'(ite (= {sel} {bv(i,B)}) {kind}{i} {ans})'
 return ans
s=['(set-logic QF_BV)',f'(set-option :timeout {a.limit*1000})',f'(set-option :sat.random_seed {a.seed})','(set-option :produce-models true)']
for i in range(n):
 f=sum(1<<j for j,x in enumerate(rows) if x>>i&1)
 s.extend([f'(define-fun f{i} () (_ BitVec {W}) {bv(f,W)})',f'(define-fun c{i} () (_ BitVec 2) {bv(1 if i<p else 2,2)})'])
for j,(op,u,v) in enumerate(seed):
 m=n+j
 s.extend([f'(declare-const a{j} (_ BitVec {B}))',f'(declare-const b{j} (_ BitVec {B}))',f'(declare-const o{j} Bool)',f'(declare-const z{j} Bool)',f'(assert (bvule a{j} b{j}))',f'(assert (bvult b{j} {bv(m,B)}))'])
 for pos in ['a','b']:
  for kind,width in [('f',W),('c',2)]:s.append(f'(define-fun {pos}{kind}{j} () (_ BitVec {width}) {select(pos+str(j),kind,m)})')
 s.extend([f'(define-fun f{m} () (_ BitVec {W}) (ite z{j} af{j} (ite o{j} (bvor af{j} bf{j}) (bvand af{j} bf{j}))))',f'(define-fun c{m} () (_ BitVec 2) (ite z{j} ac{j} (ite o{j} (bvor ac{j} bc{j}) #b00)))',f'(assert (not (= c{m} #b11)))',f'(define-fun e{j} () Bool (or z{j} (not (= o{j} {str(op).lower()})) (not (= a{j} {bv(u,B)})) (not (= b{j} {bv(v,B)}))))'])
zsum=fold('bvadd',[f'(ite z{j} {bv(1,C)} {bv(0,C)})' for j in range(k)],bv(0,C))
esum=fold('bvadd',[f'(ite e{j} {bv(1,C)} {bv(0,C)})' for j in range(k)],bv(0,C))
s.extend([f'(assert (= {zsum} {bv(a.bypasses,C)}))',f'(assert (bvule {esum} {bv(a.radius,C)}))'])
target=sum(1<<j for j,x in enumerate(rows) if is_true(x));s.append(f'(assert (= f{n+k-1} {bv(target,W)}))')
text='\n'.join(s)+'\n(check-sat-using (then simplify solve-eqs bit-blast sat))\n';Path(a.out+'.smt2').write_text(text);Path(a.out+'.seed.json').write_text(json.dumps({'n':n,'rows':rows,'edges':E,'gates':seed}))
z=ctypes.CDLL('libz3.so.4');z.Z3_mk_config.restype=ctypes.c_void_p;z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p;z.Z3_del_config.argtypes=[ctypes.c_void_p];z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p;z.Z3_del_context.argtypes=[ctypes.c_void_p]
cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg);start=time.monotonic();result=z.Z3_eval_smtlib2_string(ctx,text.encode()).decode();elapsed=time.monotonic()-start
if result.strip()=='sat':
 names=' '.join(v+str(j) for j in range(k) for v in ['a','b','o','z'])
 result+=z.Z3_eval_smtlib2_string(ctx,('(get-value ('+names+'))').encode()).decode()
result+=f'Elapsed seconds: {elapsed}\n';Path(a.out+'.log').write_text(result);print(json.dumps(vars(a)),flush=True);print(result,flush=True);z.Z3_del_context(ctx)
