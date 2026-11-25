import argparse, ctypes, json, time
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--p',type=int,required=True);ap.add_argument('--l',type=int,required=True)
ap.add_argument('--edges',required=True);ap.add_argument('--gates',type=int,required=True)
ap.add_argument('--dirty',action='store_true');ap.add_argument('--prune-or',action='store_true');ap.add_argument('--seed',type=int,default=0);ap.add_argument('--tactic',choices=['auto','sat'],default='auto');ap.add_argument('--mixed',action='store_true');ap.add_argument('--kind',choices=['and','or'],required=True);ap.add_argument('--limit',type=int,default=120);ap.add_argument('--out',required=True)
a=ap.parse_args();p,l,n,k=a.p,a.l,a.p+a.l,a.gates
E=[tuple(map(int,e.split(','))) for e in a.edges.split(';')]
if a.prune_or and (a.kind!='or' or len(set(E))<2):ap.error('--prune-or requires OR mode and at least two distinct edges')
def is_true(x):return any((x>>v&1) and (x>>(p+w)&1) for v,w in E)
rows=sorted(set((1<<v)|(1<<(p+w)) for v,w in E))
rows += [x for x in range(1<<n) if not is_true(x) and all((x>>i&1) or is_true(x|(1<<i)) for i in range(n))]
W=len(rows);ones=(1<<W)-1;positive=sum(1<<j for j,x in enumerate(rows) if is_true(x))
main='bvand' if a.kind=='and' else 'bvor';free='bvor' if a.kind=='and' else 'bvand';empty=0 if a.kind=='and' else ones
s=['(set-logic QF_BV)',f'(set-option :sat.random_seed {a.seed})',f'(set-option :smt.random_seed {a.seed})',f'(set-option :timeout {a.limit*1000})','(set-option :produce-models true)']
def bv(x):return f'(_ bv{x} {W})'
def fold(op,xs,default):
 if not xs:return default
 if len(xs)==1:return xs[0]
 return '('+op+' '+' '.join(xs)+')'
values=[]
for i in range(n):
 f=sum(1<<j for j,x in enumerate(rows) if x>>i&1)
 s.append(f'(define-fun f{i} () (_ BitVec {W}) {bv(f)})')
def operand(name,indices):
 sels=[name+'s'+str(i) for i in indices];values.extend(sels)
 for v in sels:s.append(f'(declare-const {v} Bool)')
 s.append('(assert '+fold('or',sels,'false')+')')
 exprs=[f'(ite {v} f{i} {bv(empty)})' for v,i in zip(sels,indices)]
 s.append(f'(define-fun {name} () (_ BitVec {W}) {fold(free,exprs,bv(empty))})')
 if a.kind=='and' and not a.mixed:
  ps=[name+'s'+str(i) for i in indices if i<p];ls=[name+'s'+str(i) for i in indices if p<=i<n]
  s.append(f'(assert (not (and {fold("or",ps,"false")} {fold("or",ls,"false")})))')
for j in range(k):
 m=n+j
 operand('a'+str(j),list(range(m)));operand('b'+str(j),list(range(m)))
 s.append(f'(assert (bvule a{j} b{j}))')
 s.append(f'(define-fun f{m} () (_ BitVec {W}) ({main} a{j} b{j}))')
 if a.prune_or and a.kind=='or':
  s.append(f'(assert (not (= (bvand (bvand a{j} (bvnot b{j})) {bv(positive)}) {bv(0)})))')
  s.append(f'(assert (not (= (bvand (bvand b{j} (bvnot a{j})) {bv(positive)}) {bv(0)})))')
 # Repeated functions are allowed, including AND buffers that hide input colours.
operand('out',list(range(n,n+k)) if a.kind=='and' else list(range(n+k)))
target=sum(1<<j for j,x in enumerate(rows) if is_true(x))
s.append(f'(assert (= out {bv(target)}))')
if a.dirty:
 if a.kind!='and':ap.error('--dirty is an AND-count query')
 ds=[f'(not (= (bvand f{n+j} {bv(ones ^ positive)}) {bv(0)}))' for j in range(k)]
 s.append('(assert '+fold('or',ds,'false')+')')
check='(check-sat)' if a.tactic=='auto' else '(check-sat-using (then simplify solve-eqs bit-blast sat))'
text='\n'.join(s)+'\n'+check+'\n';Path(a.out+'.smt2').write_text(text)
z=ctypes.CDLL('libz3.so.4');z.Z3_mk_config.restype=ctypes.c_void_p;z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p;z.Z3_del_config.argtypes=[ctypes.c_void_p];z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p;z.Z3_del_context.argtypes=[ctypes.c_void_p]
cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg)
t=time.monotonic();result=z.Z3_eval_smtlib2_string(ctx,text.encode()).decode();elapsed=time.monotonic()-t
if result.strip()=='sat':result+=z.Z3_eval_smtlib2_string(ctx,('(get-value ('+' '.join(values)+'))').encode()).decode()
result+=f'Elapsed seconds: {elapsed}\n';Path(a.out+'.log').write_text(result)
print(json.dumps(vars(a)),flush=True);print(result,flush=True);z.Z3_del_context(ctx)
