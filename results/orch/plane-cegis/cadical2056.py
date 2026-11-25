import argparse, ctypes as C, datetime, importlib.util, json, os, resource, signal, subprocess, time
from pathlib import Path

pa=argparse.ArgumentParser()
pa.add_argument('--query',required=True)
pa.add_argument('--data',required=True)
pa.add_argument('--size',type=int,required=True)
pa.add_argument('--seconds',type=int,required=True)
pa.add_argument('--prefix',required=True)
args=pa.parse_args()
resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,4*1024**3))
base=Path(args.prefix)
base.parent.mkdir(exist_ok=True)
spec=importlib.util.spec_from_file_location('zs',str(Path(__file__).with_name('synth-2056.py')))
z=importlib.util.module_from_spec(spec);spec.loader.exec_module(z)
def fn(name,rest,types):return z.bind(name,rest,types)
P,S,U=z.P,z.S,z.U
B=C.c_bool
cfg=z.mkcfg();z.setcfg(cfg,b'model',b'true');ctx=z.mkctx(cfg);z.delcfg(cfg)
solver=z.mksol(ctx);z.inc(ctx,solver);z.parse(ctx,solver,Path(args.query).read_bytes())
get_assertions=fn('Z3_solver_get_assertions',P,[P,P])
vector_size=fn('Z3_ast_vector_size',U,[P,P])
vector_get=fn('Z3_ast_vector_get',P,[P,P,U])
mkgoal=fn('Z3_mk_goal',P,[P,B,B,B]);goalinc=fn('Z3_goal_inc_ref',None,[P,P]);goalassert=fn('Z3_goal_assert',None,[P,P,P])
goalsize=fn('Z3_goal_size',U,[P,P]);goalformula=fn('Z3_goal_formula',P,[P,P,U])
mktactic=fn('Z3_mk_tactic',P,[P,S]);tacticinc=fn('Z3_tactic_inc_ref',None,[P,P])
andthen=fn('Z3_tactic_and_then',P,[P,P,P]);apply=fn('Z3_tactic_apply',P,[P,P,P]);applyinc=fn('Z3_apply_result_inc_ref',None,[P,P])
subgoal=fn('Z3_apply_result_get_subgoal',P,[P,P,U]);numsub=fn('Z3_apply_result_get_num_subgoals',U,[P,P])
getdecl=fn('Z3_get_app_decl',P,[P,P]);kind=fn('Z3_get_decl_kind',U,[P,P]);nargs=fn('Z3_get_app_num_args',U,[P,P]);arg=fn('Z3_get_app_arg',P,[P,P,U]);astid=fn('Z3_get_ast_id',U,[P,P]);aststr=fn('Z3_ast_to_string',S,[P,P])
assertions=get_assertions(ctx,solver)
fn('Z3_ast_vector_inc_ref',None,[P,P])(ctx,assertions)
goal=mkgoal(ctx,True,False,False);goalinc(ctx,goal)
for i in range(vector_size(ctx,assertions)):goalassert(ctx,goal,vector_get(ctx,assertions,i))
tactics=[]
for name in [b'simplify',b'propagate-values',b'solve-eqs',b'simplify',b'bit-blast',b'tseitin-cnf']:
 t=mktactic(ctx,name);tacticinc(ctx,t);tactics.append(t)
tac=tactics[0]
for t in tactics[1:]:tac=andthen(ctx,tac,t);tacticinc(ctx,tac)
started=time.time()
res=apply(ctx,tac,goal);applyinc(ctx,res)
assert numsub(ctx,res)==1
cnfgoal=subgoal(ctx,res,0);goalinc(ctx,cnfgoal)
clauses=[];index={};atoms=[]
for k in range(goalsize(ctx,cnfgoal)):
 f=goalformula(ctx,cnfgoal,k)
 literals=[arg(ctx,f,i) for i in range(nargs(ctx,f))] if kind(ctx,getdecl(ctx,f))==262 else[f]
 cl=[];tautology=False
 for lit in literals:
  sign=1
  if kind(ctx,getdecl(ctx,lit))==265:sign=-1;lit=arg(ctx,lit,0)
  typ=kind(ctx,getdecl(ctx,lit))
  if typ in (256,257):
   true=(typ==256)==(sign==1)
   if true:tautology=True;break
   continue
  assert nargs(ctx,lit)==0,(typ,aststr(ctx,lit))
  identity=astid(ctx,lit)
  if identity not in index:index[identity]=len(atoms)+1;atoms.append(lit)
  cl.append(sign*index[identity])
 if not tautology:clauses.append(cl)
cnf=base.with_suffix('.cnf')
with cnf.open('w')as f:
 f.write(f'p cnf {len(atoms)} {len(clauses)}\n')
 for cl in clauses:f.write(' '.join(map(str,cl))+' 0\n')
base.with_suffix('.mapping.json').write_text(json.dumps({'variables':[aststr(ctx,a).decode()for a in atoms],'source_query':str(Path(args.query).resolve())},indent=2))
metadata={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'variables':len(atoms),'clauses':len(clauses),'conversion_seconds':time.time()-started,'size':args.size,'seconds_limit':args.seconds}
print(json.dumps(metadata),flush=True)
exe='/tmp/oec/pequalnp-pilot-121/toolchain/lean-4.36.0-linux/bin/cadical'
with base.with_suffix('.stdout').open('w')as out,base.with_suffix('.stderr').open('w')as err:
 proc=subprocess.Popen([exe,'-t',str(args.seconds),'-w',str(base.with_suffix('.sol')),str(cnf)],stdout=out,stderr=err,start_new_session=True)
 base.with_suffix('.process.json').write_text(json.dumps({'wrapper_pid':os.getpid(),'solver_pid':proc.pid,'prefix':str(base)}))
 termination_signal=[None]
 def terminate(sig,frame):
  termination_signal[0]=sig
  if proc.returncode is not None:raise SystemExit(128+sig)
  try:os.killpg(proc.pid,sig)
  except ProcessLookupError:pass
 signal.signal(signal.SIGTERM,terminate)
 proc.wait()
 if termination_signal[0]is not None:raise SystemExit(128+termination_signal[0])
metadata['exit_code']=proc.returncode
if proc.returncode==10:
 text=base.with_suffix('.sol').read_text();assignment={}
 for line in text.splitlines():
  if line.startswith('v '):
   for v in map(int,line[2:].split()):
    if v:assignment[abs(v)]=v>0
 assert set(assignment)==set(range(1,len(atoms)+1))
 assert all(any(assignment[abs(v)]==(v>0)for v in cl)for cl in clauses)
 mkmodel=fn('Z3_mk_model',P,[P]);modelinc=fn('Z3_model_inc_ref',None,[P,P]);addconst=fn('Z3_add_const_interp',None,[P,P,P,P]);mktrue=fn('Z3_mk_true',P,[P]);mkfalse=fn('Z3_mk_false',P,[P]);convert=fn('Z3_goal_convert_model',P,[P,P,P])
 model=mkmodel(ctx);modelinc(ctx,model)
 for i,a in enumerate(atoms,1):addconst(ctx,model,getdecl(ctx,a),mktrue(ctx)if assignment[i]else mkfalse(ctx))
 print('stage: reconstruct original model',flush=True)
 original=convert(ctx,cnfgoal,model);modelinc(ctx,original)
 base.with_suffix('.original-model.txt').write_text(z.modelstr(ctx,original).decode())
 print('stage: verify original assertions',flush=True)
 evalmodel=fn('Z3_model_eval',B,[P,P,P,B,C.POINTER(P)]);boolvalue=fn('Z3_get_bool_value',C.c_int,[P,P]);numeral=fn('Z3_get_numeral_uint',B,[P,P,C.POINTER(U)]);mkbvsort=fn('Z3_mk_bv_sort',P,[P,U]);mkconst=fn('Z3_mk_const',P,[P,P,P])
 def ev(a):
  r=P();assert evalmodel(ctx,original,a,True,C.byref(r));return r
 for i in range(vector_size(ctx,assertions)):
  assert boolvalue(ctx,ev(vector_get(ctx,assertions,i)))==1,('original assertion failed',i)
 print('stage: extract gate values',flush=True)
 data=json.loads(Path(args.data).read_text());n=data['n'];gates=[]
 for j in range(args.size):
  decoded={}
  for name,bits in [('o',2),('a',(n+j).bit_length()),('b',(n+j).bit_length())]:
   a=mkconst(ctx,z.mkstr(ctx,f'{name}{j}'.encode()),mkbvsort(ctx,bits));value=U();assert numeral(ctx,ev(a),C.byref(value));decoded[name]=value.value
  gates.append([decoded['o'],decoded['a'],decoded['b']])
 assert all(op in(0,1)and 0<=a<n+j and 0<=b<n+j for j,(op,a,b)in enumerate(gates))
 mismatches=[]
 for row in data['rows']:
  values=[(row>>i)&1 for i in range(n)]
  for op,a,b in gates:values.append(values[a]&values[b]if op==0 else values[a]|values[b])
  target=any((row>>a)&(row>>b)&1 for a,b in data['edges'])
  if values[-1]!=target:mismatches.append(row)
 metadata.update({'status':'sat query; full boundary validated' if not mismatches else 'sat query; invalid full-boundary candidate','gates':gates,'full_boundary_mismatches':mismatches,'original_smt_assertions_verified':vector_size(ctx,assertions)})
 if n<=20:
  values=[int(('1'*(1<<i)+'0'*(1<<i))*(1<<(n-i-1)),2)for i in range(n)];target=0
  for a,b in data['edges']:target|=values[a]&values[b]
  for op,a,b in gates:values.append(values[a]&values[b]if op==0 else values[a]|values[b])
  metadata['exhaustive_mismatches']=(target^values[-1]).bit_count();metadata['exhaustive_assignments']=1<<n
  if metadata['exhaustive_mismatches']:metadata['status']='sat query; invalid exhaustive candidate'
elif proc.returncode==20:metadata['status']='unsat; external solver only, not Lean checked'
elif proc.returncode==0:metadata['status']='unknown; time or resource limit'
else:metadata['status']='solver error'
base.with_suffix('.json').write_text(json.dumps(metadata,indent=2))
print(json.dumps(metadata),flush=True)
z.delctx(ctx)
