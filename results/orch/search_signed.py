import ctypes,ctypes.util,sys,time,json,re
from pathlib import Path
s=int(sys.argv[1]);limit=int(sys.argv[2]) if len(sys.argv)>2 else 300000
T=4269860992*2**32+4261445632;n=6;rows=list(range(64));vs={};clauses=[]
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
 m=6+j
 for side in ['a','b']:
  add(*(sel(j,side,k) for k in range(m)));amo([sel(j,side,k) for k in range(m)])
 for a in range(m):
  for b in range(a,m):add(-sel(j,'a',b),-sel(j,'b',a))
 ops=[v(f'op_{j}_{d}') for d in range(4)];add(*ops);amo(ops)
 for r in rows:
  for side in ['a','b']:
   q=v(f'{side}val_{j}_{r}')
   for k in range(m):
    p=sel(j,side,k)
    if k<6:add(-p,q if r>>k&1 else -q)
    else:
     x=w(k-6,r);add(-p,-q,x);add(-p,q,-x)
  a=v(f'aval_{j}_{r}');b=v(f'bval_{j}_{r}');c=w(j,r)
  for d,o in enumerate(ops):
   if d==1:
    add(-o,c,-a);add(-o,c,-b);add(-o,-c,a,b)
   else:
    x=-a if d==3 else a;y=-b if d==2 else b
    add(-o,-c,x);add(-o,-c,y);add(-o,c,-x,-y)
for r in rows:add(w(s-1,r) if T>>r&1 else -w(s-1,r))
for j in range(s-1):add(*(sel(k,side,6+j) for k in range(j+1,s) for side in ['a','b']))
for i in range(6):add(*(sel(j,side,i) for j in range(s) for side in ['a','b']))
for j in range(s-1):
 for a in range(6+j):
  for b in range(a):add(-sel(j,'b',a),-sel(j+1,'b',b))
for j in range(s):
 for side in ['a','b']:
  for i in [1,2]:
   earlier=[sel(k,z,i-1) for k in range(j) for z in ['a','b']]
   if side=='b':earlier.append(sel(j,'a',i-1))
   add(-sel(j,side,i),*earlier)
def lit(i):return 'v'+str(i) if i>0 else '(not v'+str(-i)+')'
body='(set-option :timeout '+str(limit)+')\n(set-option :produce-models true)\n'
body+=''.join('(declare-const v'+str(i)+' Bool)\n' for i in range(1,len(vs)+1))
body+=''.join('(assert (or '+' '.join(map(lit,c))+'))\n' for c in clauses)
body+='(check-sat)\n'
base=Path('/tmp/oec/pequalnp-pilot-160')/f'search-signed-{s}'
base.with_suffix('.smt2').write_text(body);base.with_suffix('.names.json').write_text(json.dumps(vs))
print('Problem signed',s,len(rows),len(vs),len(clauses),flush=True)
z=ctypes.CDLL(ctypes.util.find_library('z3'));z.Z3_mk_config.restype=ctypes.c_void_p
z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p
z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);t=time.time();out=z.Z3_eval_smtlib2_string(ctx,body.encode()).decode()
print(out,'elapsed',time.time()-t,flush=True)
if out.strip()=='sat':
 model=z.Z3_eval_smtlib2_string(ctx,b'(get-model)').decode();base.with_suffix('.model').write_text(model)
 true=set(map(int,re.findall(r'\(define-fun v(\d+) \(\) Bool\s+true\)',model)))
 gates=[];sig=[sum(((r>>i)&1)<<r for r in range(64)) for i in range(6)]
 for j in range(s):
  a=next(k for k in range(6+j) if vs[f'a_{j}_{k}'] in true);b=next(k for k in range(6+j) if vs[f'b_{j}_{k}'] in true)
  d=next(d for d in range(4) if vs[f'op_{j}_{d}'] in true);gates.append((d,a,b))
  sig.append([sig[a]&sig[b],sig[a]|sig[b],sig[a]&~sig[b],~sig[a]&sig[b]][d])
 print('gates',gates,'output',s+5,'table',hex(sig[-1]),'correct',sig[-1]==T,flush=True)
 base.with_suffix('.gates.json').write_text(json.dumps(gates))
