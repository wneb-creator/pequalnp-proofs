import ctypes,ctypes.util,sys,time,json,re
from pathlib import Path
s=int(sys.argv[1]);mode=sys.argv[2];limit=int(sys.argv[3]) if len(sys.argv)>3 else 120000
T=4269860992*2**32+4261445632
rows=list(range(64))
if mode=='mono':
 rows=[r for r in rows if ((T>>r&1) and all(not(T>>(r^(1<<j))&1) for j in range(6) if r>>j&1)) or (not(T>>r&1) and all(T>>(r^(1<<j))&1 for j in range(6) if not(r>>j&1)))]
vs={};clauses=[]
def v(name):
 if name not in vs:vs[name]=len(vs)+1
 return vs[name]
def add(*lits):clauses.append(lits)
def amo(seq):
 for i,x in enumerate(seq):
  for y in seq[:i]:add(-x,-y)
def sel(j,side,k):return v(f'{side}_{j}_{k}')
def w(j,r):return v(f'w_{j}_{r}')
for j in range(s):
 n=6+j
 for side in ['a','b']:
  add(*(sel(j,side,k) for k in range(n)))
  amo([sel(j,side,k) for k in range(n)])
 for a in range(n):
  for b in range(a,n):
   if mode=='mono':add(-sel(j,'a',b),-sel(j,'b',a))
   else:add(-sel(j,'a',b),-sel(j,'b',a),v(f'not_{j}'))
 if mode!='mono':
  # A NOT is represented with its otherwise unused second source equal to its first.
  for a in range(n):add(-v(f'not_{j}'),-sel(j,'a',a),sel(j,'b',a))
 for r in rows:
  for side in ['a','b']:
   q=v(f'{side}val_{j}_{r}')
   for k in range(n):
    p=sel(j,side,k)
    if k<6:add(-p,q if r>>k&1 else -q)
    else:
     x=w(k-6,r);add(-p,-q,x);add(-p,q,-x)
  a=v(f'aval_{j}_{r}');b=v(f'bval_{j}_{r}');c=w(j,r);o=v(f'or_{j}')
  guard=[] if mode=='mono' else [v(f'not_{j}')]
  add(*guard,o,-c,a);add(*guard,o,-c,b);add(*guard,o,c,-a,-b)
  add(*guard,-o,c,-a);add(*guard,-o,c,-b);add(*guard,-o,-c,a,b)
  if mode!='mono':
   q=v(f'not_{j}');add(-q,c,a);add(-q,-c,-a)
for r in rows:add(w(s-1,r) if T>>r&1 else -w(s-1,r))
# Every intermediate gate is used.
for j in range(s-1):add(*(sel(k,side,6+j) for k in range(j+1,s) for side in ['a','b']))
if mode!='mono':
 add(*(v(f'not_{j}') for j in range(s)))
 if mode=='one':amo([v(f'not_{j}') for j in range(s)])
# Every essential primary input is used.
for i in range(6):add(*(sel(j,side,i) for j in range(s) for side in ['a','b']))
# Order independent gates by their second operand. Any DAG admits this ordering.
# Disabled initially to keep model soundness transparent.
def lit(i):return 'v'+str(i) if i>0 else '(not v'+str(-i)+')'
body='(set-option :timeout '+str(limit)+')\n(set-option :produce-models true)\n'
body+=''.join('(declare-const v'+str(i)+' Bool)\n' for i in range(1,len(vs)+1))
body+=''.join('(assert (or '+' '.join(map(lit,c))+'))\n' for c in clauses)
body+='(check-sat)\n'
base=Path('/tmp/oec/pequalnp-pilot-160')/f'search-{mode}-{s}'
base.with_suffix('.smt2').write_text(body)
base.with_suffix('.names.json').write_text(json.dumps(vs))
print('Problem',mode,s,len(rows),len(vs),len(clauses),flush=True)
z=ctypes.CDLL(ctypes.util.find_library('z3'))
z.Z3_mk_config.restype=ctypes.c_void_p;z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p
z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);t=time.time()
out=z.Z3_eval_smtlib2_string(ctx,body.encode()).decode()
print(out,'elapsed',time.time()-t,flush=True)
if out.strip()=='sat':
 model=z.Z3_eval_smtlib2_string(ctx,b'(get-model)').decode();base.with_suffix('.model').write_text(model)
 true=set(map(int,re.findall(r'\(define-fun v(\d+) \(\) Bool\s+true\)',model)))
 gates=[];sig=[sum(((r>>i)&1)<<r for r in range(64)) for i in range(6)]
 for j in range(s):
  a=next(k for k in range(6+j) if vs[f'a_{j}_{k}'] in true)
  b=next(k for k in range(6+j) if vs[f'b_{j}_{k}'] in true)
  op='not' if vs.get(f'not_{j}') in true else ('or' if vs[f'or_{j}'] in true else 'and')
  gates.append((op,a,b));sig.append((~sig[a]&((1<<64)-1)) if op=='not' else ((sig[a]|sig[b]) if op=='or' else (sig[a]&sig[b])))
 print('gates',gates,'output',s+5,'table',hex(sig[-1]),'correct',sig[-1]==T,flush=True)
 base.with_suffix('.gates.json').write_text(json.dumps(gates))
