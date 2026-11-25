import argparse, ctypes, json, math, time
from pathlib import Path
ap=argparse.ArgumentParser()
ap.add_argument('--p',type=int,required=True);ap.add_argument('--l',type=int,required=True)
ap.add_argument('--edges',required=True);ap.add_argument('--gates',type=int,required=True)
ap.add_argument('--mode',choices=['any','dirty','few_and','few_or'],default='any')
ap.add_argument('--limit',type=int,default=120);ap.add_argument('--count',type=int,default=0)
ap.add_argument('--out',required=True)
ap.add_argument('--rows',choices=['full','boundary'],default='boundary')
a=ap.parse_args();p,l,n,k=a.p,a.l,a.p+a.l,a.gates
E=[tuple(map(int,e.split(','))) for e in a.edges.split(';')];B=(n+k).bit_length()
def is_true(x):return any((x>>v&1) and (x>>(p+w)&1) for v,w in E)
if a.rows=='full': rows=list(range(1<<n))
else:
 rows=sorted(set((1<<v)|(1<<(p+w)) for v,w in E))
 rows += [x for x in range(1<<n) if not is_true(x) and all((x>>i&1) or is_true(x|(1<<i)) for i in range(n))]
W=len(rows)
def bv(x,w):return f'(_ bv{x} {w})'
def fold(op,xs,default):
 if not xs:return default
 if len(xs)==1:return xs[0]
 return '('+op+' '+' '.join(xs)+')'
def select(sel,kind,j):
 ans=kind+str(n+j-1)
 for i in range(n+j-2,-1,-1):ans=f'(ite (= {sel} {bv(i,B)}) {kind}{i} {ans})'
 return ans
s=['(set-logic QF_BV)',f'(set-option :timeout {a.limit*1000})','(set-option :produce-models true)']
for i in range(n):
 f=sum(1<<j for j,x in enumerate(rows) if x>>i&1)
 s.extend([f'(define-fun f{i} () (_ BitVec {W}) {bv(f,W)})',f'(define-fun c{i} () (_ BitVec 2) {bv(1 if i<p else 2,2)})'])
for j in range(k):
 m=n+j
 for v in ['a','b']:s.append(f'(declare-const {v}{j} (_ BitVec {B}))')
 s.extend([f'(declare-const o{j} Bool)',f'(assert (bvule a{j} b{j}))',f'(assert (bvult b{j} {bv(m,B)}))'])
 for pos in ['a','b']:
  for kind,width in [('f',W),('c',2)]:s.append(f'(define-fun {pos}{kind}{j} () (_ BitVec {width}) {select(pos+str(j),kind,j)})')
 s.extend([f'(define-fun f{m} () (_ BitVec {W}) (ite o{j} (bvor af{j} bf{j}) (bvand af{j} bf{j})))',f'(define-fun c{m} () (_ BitVec 2) (ite o{j} (bvor ac{j} bc{j}) #b00))',f'(assert (not (= c{m} #b11)))'])
 for i in range(m):s.append(f'(assert (or (not (= f{m} f{i})) (not (= c{m} c{i}))))')
 if j:
  s.append(f'(assert (or (= b{j} {bv(m-1,B)}) (bvugt f{m} f{m-1}) (and (= f{m} f{m-1}) (bvugt c{m} c{m-1}))))')
for j in range(k-1):
 users=[f'(= {pos}{q} {bv(n+j,B)})' for q in range(j+1,k) for pos in ['a','b']]
 s.append('(assert '+fold('or',users,'false')+')')
target=sum(1<<j for j,x in enumerate(rows) if is_true(x))
s.append(f'(assert (= f{n+k-1} {bv(target,W)}))')
if a.mode=='dirty':
 ds=[f'(and (not o{j}) (not (= (bvand f{n+j} {bv((1<<W)-1-target,W)}) {bv(0,W)})))' for j in range(k)]
 s.append('(assert '+fold('or',ds,'false')+')')
if a.mode in ['few_and','few_or']:
 terms=[f'(ite {"(not o"+str(j)+")" if a.mode=="few_and" else "o"+str(j)} {bv(1,B)} {bv(0,B)})' for j in range(k)]
 s.append(f'(assert (bvult {fold("bvadd",terms,bv(0,B))} {bv(a.count,B)}))')
text='\n'.join(s)+'\n(check-sat)\n'
Path(a.out+'.smt2').write_text(text)
z=ctypes.CDLL('libz3.so.4')
z.Z3_mk_config.restype=ctypes.c_void_p
z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p
z.Z3_del_config.argtypes=[ctypes.c_void_p]
z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
z.Z3_del_context.argtypes=[ctypes.c_void_p]
cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg)
t=time.monotonic();result=z.Z3_eval_smtlib2_string(ctx,text.encode()).decode();elapsed=time.monotonic()-t
if result.strip()=='sat':
 values=' '.join(v+str(j) for j in range(k) for v in ['o','a','b'])
 result+=z.Z3_eval_smtlib2_string(ctx,f'(get-value ({values}))'.encode()).decode()
result+=f'Elapsed seconds: {elapsed}\n'
Path(a.out+'.log').write_text(result)
print(json.dumps(vars(a)),flush=True);print(result,flush=True)
z.Z3_del_context(ctx)
