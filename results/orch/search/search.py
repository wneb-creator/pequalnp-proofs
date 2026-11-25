import argparse, ctypes, ctypes.util, itertools, json, re, time
from pathlib import Path
P=argparse.ArgumentParser()
P.add_argument('--case',default='and_edge')
P.add_argument('--timeout-ms',type=int,default=240000)
P.add_argument('--gates',type=int,default=19)
P.add_argument('--seed',type=int,default=1)
P.add_argument('--allow-unused',action='store_true')
P.add_argument('--local')
P.add_argument('--radius',type=int,default=5)
P.add_argument('--not-count',type=int)
P.add_argument('--distinct',action='store_true')
P.add_argument('--ordered',action='store_true')
P.add_argument('--max-nots',type=int)
P.add_argument('--eager-sat',action='store_true')
P.add_argument('--mutable')
P.add_argument('--brief',action='store_true')
args=P.parse_args()
N=args.gates
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x):return any((x>>a&1) and (x>>b&1) for a,b in E)
z=ctypes.CDLL(ctypes.util.find_library('z3'))
z.Z3_mk_config.restype=ctypes.c_void_p
z.Z3_set_param_value.argtypes=[ctypes.c_void_p,ctypes.c_char_p,ctypes.c_char_p]
z.Z3_mk_context.argtypes=[ctypes.c_void_p]
z.Z3_mk_context.restype=ctypes.c_void_p
z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p]
z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
cfg=z.Z3_mk_config(); z.Z3_set_param_value(cfg,b'timeout',str(args.timeout_ms).encode())
ctx=z.Z3_mk_context(cfg)
def smt(s): return z.Z3_eval_smtlib2_string(ctx,s.encode()).decode()
def bv(i,k=5):return f'(_ bv{i} {k})'
s=['(set-logic QF_BV)',f'(set-option :timeout {args.timeout_ms})',f'(set-option :smt.random_seed {args.seed})',f'(set-option :sat.random_seed {args.seed})']
for i in range(N):
 s += [f'(declare-const a{i} (_ BitVec 5))',f'(declare-const b{i} (_ BitVec 5))',f'(declare-const o{i} (_ BitVec 2))',
       f'(assert (bvult a{i} {bv(11+i)}))',f'(assert (bvult b{i} {bv(11+i)}))',
       f'(assert (=> (bvule o{i} {bv(1,2)}) (bvule a{i} b{i})))',
       f'(assert (=> (bvuge o{i} {bv(2,2)}) (= b{i} {bv(0)})))',
       f'(assert (=> (= o{i} {bv(3,2)}) (= a{i} {bv(0)})))']
s += ['(assert (or '+' '.join(f'(= o{i} {bv(2,2)})' for i in range(N))+'))']
if args.max_nots is not None:
 s += [f'(assert ((_ at-most {args.max_nots}) '+' '.join(f'(= o{i} {bv(2,2)})' for i in range(N))+'))']
if args.ordered:
 ms=[f'(ite (bvule o{i} {bv(1,2)}) b{i} a{i})' for i in range(N)]
 for i in range(N-1):
  s += [f'(assert (bvule {ms[i]} {ms[i+1]}))',f'(assert (=> (= {ms[i]} {ms[i+1]}) (bvule o{i} o{i+1})))',f'(assert (=> (and (= {ms[i]} {ms[i+1]}) (= o{i} o{i+1})) (bvule a{i} a{i+1})))']
if args.not_count is not None:
 ns=[f'(= o{i} {bv(2,2)})' for i in range(N)]
 s += [f'(assert ((_ at-most {args.not_count}) '+' '.join(ns)+'))', f'(assert ((_ at-least {args.not_count}) '+' '.join(ns)+'))']
 for i in range(N):s += [f'(assert (not (= o{i} {bv(3,2)})))']
# Restrict to circuits where every gate is used, for the first search.
for i in range(0 if args.allow_unused else N-1):
 s += ['(assert (or '+' '.join(f'(or (= a{j} {bv(11+i)}) (and (bvule o{j} {bv(1,2)}) (= b{j} {bv(11+i)})))' for j in range(i+1,N))+'))']
if args.local:
 gates=json.loads(Path(args.local).read_text())
 assert len(gates)==N
 changes=[]
 for i,(o,a,b) in enumerate(gates):
  if o<=1 and a>b:a,b=b,a
  if o>=2:b=0
  changes.append(f'(or (not (= o{i} {bv(o,2)})) (not (= a{i} {bv(a)})) (not (= b{i} {bv(b)})))')
 if args.mutable:
  mutable={int(i) for i in args.mutable.split(',')}
  for i,ch in enumerate(changes):
   if i not in mutable:s += ['(assert (not '+ch+'))']
 else:
  s += [f'(assert ((_ at-most {args.radius}) '+ ' '.join(changes)+'))']
if args.case!='any':
 op,a,b={'and_edge':(0,0,1),'and_nonedge':(0,0,2),'or_edge':(1,0,1),'or_nonedge':(1,0,2),'not':(2,0,0),'true':(3,0,0)}[args.case]
 s += [f'(assert (= o0 {bv(op,2)}))',f'(assert (= a0 {bv(a)}))',f'(assert (= b0 {bv(b)}))']
print('start',time.time(),'case',args.case,'gates',N,flush=True)
print(smt('\n'.join(s)),flush=True)
seen=set()
# All assignments of weights <=2, plus maximal negative assignments and near full inputs.
initial=[x for x in range(1024) if x.bit_count()<=2 or x.bit_count()>=9 or (not target(x) and all(target(x|(1<<i)) for i in range(10) if not x>>i&1))]
new=initial
for stage in range(40):
 seen.update(new); k=len(new)
 tt=[sum(((x>>j)&1)<<t for t,x in enumerate(new)) for j in range(10)]+[0]
 truth=sum(int(target(x))<<t for t,x in enumerate(new))
 lines=[]
 for i in range(N):
  lines += [f'(declare-const g{stage}_{i} (_ BitVec {k}))']
  def sel(v):
   r=bv(0,k)
   for j in range(11+i):
    val=bv(tt[j],k) if j<11 else f'g{stage}_{j-11}'
    r=f'(ite (= {v} {bv(j)}) {val} {r})'
   return r
  aa,bb=sel(f'a{i}'),sel(f'b{i}')
  lines += [f'(assert (= g{stage}_{i} (ite (= o{i} {bv(0,2)}) (bvand {aa} {bb}) (ite (= o{i} {bv(1,2)}) (bvor {aa} {bb}) (ite (= o{i} {bv(2,2)}) (bvnot {aa}) {bv((1<<k)-1,k)})))))']
 lines += [f'(assert (= g{stage}_{N-1} {bv(truth,k)}))']
 if args.distinct and stage==0:
  lines += ['(assert (distinct '+ ' '.join([bv(t,k) for t in tt]+[bv((1<<k)-1,k)]+[f'g{stage}_{i}' for i in range(N)])+'))']
 check='(check-sat-using (then simplify solve-eqs bit-blast pb2bv sat))' if args.eager_sat else '(check-sat)'
 res=smt('\n'.join(lines)+'\n'+check)
 print('stage',stage,'examples',len(seen),'time',time.time(),'result',res,flush=True)
 if res.strip()!='sat':
  print(smt('(get-info :reason-unknown)' if args.brief else '(get-info :reason-unknown)\n(get-info :all-statistics)'),flush=True)
  break
 model=smt('(get-value ('+' '.join(f'{v}{i}' for i in range(N) for v in ['a','b','o'])+'))')
 vals={v:int(d,2 if base=='b' else 16) for v,base,d in re.findall(r'\(([abo]\d+) #([bx])([0-9a-f]+)\)',model)}
 gates=[(vals[f'o{i}'],vals[f'a{i}'],vals[f'b{i}']) for i in range(N)]
 def calc(x):
  w=[bool(x>>j&1) for j in range(10)]+[False]
  for op,a,b in gates:w.append((w[a] and w[b]) if op==0 else (w[a] or w[b]) if op==1 else not w[a] if op==2 else True)
  return w[-1]
 bad=[x for x in range(1024) if calc(x)!=target(x)]
 print('candidate',gates,'bad',len(bad),flush=True)
 if not bad:
  print('WITNESS',json.dumps(gates),flush=True)
  Path(f'/tmp/oec/pequalnp-pilot-103/counterexample/witness-{args.case}.json').write_text(json.dumps(gates))
  break
 # Spread sample across weights and signs, preserving all previous assignments.
 new=[]
 for wt in range(11):
  for t in [False,True]:
   group=[x for x in bad if x.bit_count()==wt and target(x)==t]
   new.extend(group[:6])
 print('new_examples',new,flush=True)
