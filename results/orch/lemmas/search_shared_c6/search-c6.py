import argparse,ctypes,itertools,json,time,sys
from pathlib import Path
P=argparse.ArgumentParser(); P.add_argument('--gates',type=int,default=19); P.add_argument('--shard',type=int,default=0); P.add_argument('--timeout',type=int,default=60000); P.add_argument('--rounds',type=int,default=100); P.add_argument('--seed',type=int,default=-1); P.add_argument('--edits',type=int,default=3); P.add_argument('--critical',action='store_true'); P.add_argument('--seedfile',default='/tmp/oec/pequalnp-pilot-92/local-seeds.json'); P.add_argument('--min-not',type=int,default=1); P.add_argument('--max-not',type=int,default=4); P.add_argument('--prefix',default=''); P.add_argument('--allow-redundant',action='store_true'); A=P.parse_args()
prefix=json.loads(Path(A.prefix).read_text()) if A.prefix else []
prefix=[({'and':0,'or':1,'not':2}.get(o,o),a,b) for o,a,b in prefix]
nbase=6+len(prefix)
z=ctypes.CDLL('/usr/lib/x86_64-linux-gnu/libz3.so.4'); ptr=ctypes.c_void_p; ui=ctypes.c_uint

def bind(n,args,result=ptr):
 f=getattr(z,n); f.argtypes=args; f.restype=result; return f
cfg=bind('Z3_mk_config',[])(); bind('Z3_set_param_value',[ptr,ctypes.c_char_p,ctypes.c_char_p],None)(cfg,b'model',b'true')
c=bind('Z3_mk_context',[ptr])(cfg); bind('Z3_del_config',[ptr],None)(cfg)
sort=bind('Z3_mk_bool_sort',[ptr])(c); sym=bind('Z3_mk_int_symbol',[ptr,ctypes.c_int]); const=bind('Z3_mk_const',[ptr,ptr,ptr]); mktrue=bind('Z3_mk_true',[ptr]); mkfalse=bind('Z3_mk_false',[ptr]); mknot=bind('Z3_mk_not',[ptr,ptr]); mkand=bind('Z3_mk_and',[ptr,ui,ctypes.POINTER(ptr)]); mkor=bind('Z3_mk_or',[ptr,ui,ctypes.POINTER(ptr)]); mkeq=bind('Z3_mk_eq',[ptr,ptr,ptr]); mkimplies=bind('Z3_mk_implies',[ptr,ptr,ptr]); mkite=bind('Z3_mk_ite',[ptr,ptr,ptr,ptr]); atmost=bind('Z3_mk_atmost',[ptr,ui,ctypes.POINTER(ptr),ui]); atleast=bind('Z3_mk_atleast',[ptr,ui,ctypes.POINTER(ptr),ui]); solver=bind('Z3_mk_solver_for_logic',[ptr,ptr])(c,bind('Z3_mk_string_symbol',[ptr,ctypes.c_char_p])(c,b'QF_FD')); bind('Z3_solver_inc_ref',[ptr,ptr],None)(c,solver); assertion=bind('Z3_solver_assert',[ptr,ptr,ptr],None); check=bind('Z3_solver_check',[ptr,ptr],ctypes.c_int); getmodel=bind('Z3_solver_get_model',[ptr,ptr]); modeval=bind('Z3_model_eval',[ptr,ptr,ptr,ctypes.c_bool,ctypes.POINTER(ptr)],ctypes.c_bool); boolval=bind('Z3_get_bool_value',[ptr,ptr],ctypes.c_int); modelinc=bind('Z3_model_inc_ref',[ptr,ptr],None); modeldec=bind('Z3_model_dec_ref',[ptr,ptr],None); reason=bind('Z3_solver_get_reason_unknown',[ptr,ptr],ctypes.c_char_p)
params=bind('Z3_mk_params',[ptr])(c); bind('Z3_params_inc_ref',[ptr,ptr],None)(c,params); psym=bind('Z3_mk_string_symbol',[ptr,ctypes.c_char_p]); pu=bind('Z3_params_set_uint',[ptr,ptr,ptr,ui],None); pu(c,params,psym(c,b'timeout'),A.timeout); pu(c,params,psym(c,b'random_seed'),A.shard+1); bind('Z3_solver_set_params',[ptr,ptr,ptr],None)(c,solver,params)
uid=0

def fresh():
 global uid
 uid+=1; return const(c,sym(c,uid),sort)
def arr(xs): return (ptr*len(xs))(*xs)
def OR(xs): return mkor(c,len(xs),arr(xs))
def AND(xs): return mkand(c,len(xs),arr(xs))
def NOT(x): return mknot(c,x)
def EQ(x,y): return mkeq(c,x,y)
def IMP(x,y): return mkimplies(c,x,y)
def put(x): assertion(c,solver,x)
def exactly(xs): put(OR(xs)); put(atmost(c,len(xs),arr(xs),1))
ops=[]; sa=[]; sb=[]
for i in range(A.gates):
 o=[fresh() for _ in range(3)]; a=[fresh() for _ in range(nbase+i)]; b=[fresh() for _ in range(nbase+i)]; ops.append(o);sa.append(a);sb.append(b);exactly(o);exactly(a);exactly(b)
 # Canonical commutative inputs, no useless identical inputs. NOT has b=0.
 put(IMP(o[2],b[0]))
 for k in range(nbase+i):
  put(IMP(AND([NOT(o[2]),a[k]]),OR(b[k+(0 if A.allow_redundant else 1):])))
put(atleast(c,A.gates,arr([o[2] for o in ops]),A.min_not)); put(atmost(c,A.gates,arr([o[2] for o in ops]),A.max_not))
# Automorphism orbit for the first gate: AND/OR edge/nonedge, or NOT.
shards=[(0,0,1),(0,0,2),(1,0,1),(1,0,2),(2,0,0)]
if A.seed<0:
 pass
else:
 seed=json.loads(Path(A.seedfile).read_text())[A.seed]['gates']
 changed=[]
 for i,(op,a,b) in enumerate(seed):
  if op!='not':a,b=sorted((a,b))
  else:b=0
  changed.append(NOT(AND([ops[i][{'and':0,'or':1,'not':2}[op]],sa[i][a],sb[i][b]])))
 put(atmost(c,len(changed),arr(changed),A.edits))
edges=[(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]
def target(x): return any((x>>a&1) and(x>>b&1) for a,b in edges)
patterns=set()
def addpattern(x):
 if x in patterns:return
 patterns.add(x)
 vals=[bool(x>>j&1) for j in range(6)]
 for op,a,b in prefix:vals.append(vals[a] and vals[b] if op==0 else vals[a] or vals[b] if op==1 else not vals[a])
 wires=[mktrue(c) if v else mkfalse(c) for v in vals]
 for i in range(A.gates):
  va,vb,v=fresh(),fresh(),fresh()
  for k,w in enumerate(wires): put(IMP(sa[i][k],EQ(va,w)));put(IMP(sb[i][k],EQ(vb,w)))
  put(IMP(ops[i][0],EQ(v,AND([va,vb]))));put(IMP(ops[i][1],EQ(v,OR([va,vb]))));put(IMP(ops[i][2],EQ(v,NOT(va))))
  wires.append(v)
 put(wires[-1] if target(x) else NOT(wires[-1]))
# All false inputs and all minimal positive inputs constrain the useful region.
for x in range(64):addpattern(x)
print('started',time.time(),'shard',A.shard,'variables',uid,'patterns',len(patterns),flush=True)
for rd in range(A.rounds):
 t=time.time(); status=check(c,solver); print('round',rd,'status',status,'seconds',time.time()-t,'patterns',len(patterns),'variables',uid,flush=True)
 if status==0:
  print('unknown',reason(c,solver).decode(),flush=True); continue
 if status<0:
  print('UNSAT for shard constraints',flush=True);break
 m=getmodel(c,solver);modelinc(c,m)
 def val(v):
  ret=ptr();assert modeval(c,m,v,True,ctypes.byref(ret));return boolval(c,ret)==1
 gates=[]
 for i in range(A.gates): gates.append((next(j for j,v in enumerate(ops[i]) if val(v)),next(j for j,v in enumerate(sa[i]) if val(v)),next(j for j,v in enumerate(sb[i]) if val(v))))
 modeldec(c,m)
 def evaluate(x):
  w=[bool(x>>j&1) for j in range(6)]
  for op,a,b in prefix+gates:w.append(w[a] and w[b] if op==0 else w[a] or w[b] if op==1 else not w[a])
  return w[-1]
 bad=[x for x in range(64) if evaluate(x)!=target(x)]
 print('candidate',gates,'errors',len(bad),flush=True)
 if not bad:
  Path('/tmp/oec/pequalnp-pilot-92/search-c6-witness-g'+str(len(prefix)+A.gates)+'-seed'+str(A.seed)+'.json').write_text(json.dumps({'gates':prefix+gates,'output':5+len(prefix)+A.gates},indent=2));print('WITNESS',flush=True);break
 for x in bad[:64]:addpattern(x)
