import ctypes as C, ctypes.util, sys, json, time, random
from pathlib import Path
lib=C.CDLL(ctypes.util.find_library("z3"))
def bind(n,rest,args):
 f=getattr(lib,n); f.restype=rest; f.argtypes=args; return f
P=C.c_void_p; S=C.c_char_p; U=C.c_uint
mkcfg=bind("Z3_mk_config",P,[]); setcfg=bind("Z3_set_param_value",None,[P,S,S]); mkctx=bind("Z3_mk_context",P,[P]); delcfg=bind("Z3_del_config",None,[P])
mksol=bind("Z3_mk_solver",P,[P]); inc=bind("Z3_solver_inc_ref",None,[P,P]); parse=bind("Z3_solver_from_string",None,[P,P,S]); check=bind("Z3_solver_check",C.c_int,[P,P]); getmodel=bind("Z3_solver_get_model",P,[P,P]); modelstr=bind("Z3_model_to_string",S,[P,P]); reason=bind("Z3_solver_get_reason_unknown",S,[P,P]); delctx=bind("Z3_del_context",None,[P])
mkparams=bind("Z3_mk_params",P,[P]); pinc=bind("Z3_params_inc_ref",None,[P,P]); mkstr=bind("Z3_mk_string_symbol",P,[P,S]); puint=bind("Z3_params_set_uint",None,[P,P,P,U]); sparams=bind("Z3_solver_set_params",None,[P,P,P]);
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
N=9 if "p9" in sys.argv else 10
MAXNOT=1 if N==9 else 4
E=[(a,b) for a,b in E if a<N and b<N]
def target(r): return any((r>>u)&(r>>v)&1 for u,v in E)
def solve(rows,size,seconds,seed,first):
 w=len(rows)
 def bv(v,b):return f"(_ bv{v} {b})"
 vals=[bv(sum(((r>>i)&1)<<k for k,r in enumerate(rows)),w) for i in range(N)]
 lines=["(set-logic QF_BV)"]
 for j in range(size):
  n=N+j; sw=n.bit_length()
  for v,b in [(f"a{j}",sw),(f"b{j}",sw),(f"o{j}",2),(f"v{j}",w)]:lines.append(f"(declare-const {v} (_ BitVec {b}))")
  lines += [f"(assert (bvult a{j} {bv(n,sw)}))",f"(assert (bvult b{j} {bv(n,sw)}))",f"(assert (bvult o{j} #b11))",f"(assert (ite (= o{j} #b10) (= a{j} b{j}) (bvult a{j} b{j})))"]
  def src(v):
   z=vals[-1]
   for k in reversed(range(n-1)): z=f"(ite (= {v} {bv(k,sw)}) {vals[k]} {z})"
   return z
  av,bv_=src(f"a{j}"),src(f"b{j}")
  lines.append(f"(assert (= v{j} (let ((a {av}) (b {bv_})) (ite (= o{j} #b00) (bvand a b) (ite (= o{j} #b01) (bvor a b) (bvnot a))))))")
  vals.append(f"v{j}")
 # all gates except output must be used; symmetry canonical between independent adjacent gates
 for j in range(size-1):
  used=[]
  for k in range(j+1,size):
   sw=(N+k).bit_length(); used.extend([f"(= a{k} {bv(N+j,sw)})",f"(= b{k} {bv(N+j,sw)})"])
  lines.append("(assert (or "+" ".join(used)+"))")
 lines.append("(assert (or "+" ".join(f"(= o{j} #b10)" for j in range(size)) +"))")
 count="(_ bv0 5)"
 for j in range(size):count=f"(bvadd {count} (ite (= o{j} #b10) (_ bv1 5) (_ bv0 5)))"
 lines.append(f"(assert (bvule {count} (_ bv{MAXNOT} 5)))")
 lines.append(f"(assert (= v{size-1} {bv(sum(target(r)<<k for k,r in enumerate(rows)),w)}))")
 if first is not None:
  op,a,b=first
  lines += [f"(assert (= o0 {bv(op,2)}))",f"(assert (= a0 {bv(a,4)}))",f"(assert (= b0 {bv(b,4)}))"]
 text="\n".join(lines)
 Path(f"/tmp/oec/pequalnp-pilot-121/circuit-search/query-{seed}.smt2").write_text(text)
 cfg=mkcfg(); setcfg(cfg,b"model",b"true"); ctx=mkctx(cfg); delcfg(cfg)
 sol=mksol(ctx); inc(ctx,sol)
 par=mkparams(ctx); pinc(ctx,par); puint(ctx,par,mkstr(ctx,b"timeout"),seconds*1000); puint(ctx,par,mkstr(ctx,b"random_seed"),seed); sparams(ctx,sol,par)
 parse(ctx,sol,text.encode()); status=check(ctx,sol)
 out=modelstr(ctx,getmodel(ctx,sol)).decode() if status==1 else reason(ctx,sol).decode() if status==0 else "unsat"
 print(json.dumps({"status":status,"rows":len(rows),"size":size,"seed":seed,"first":first,"result":out}),flush=True)
 Path(f"/tmp/oec/pequalnp-pilot-121/circuit-search/result-{seed}.json").write_text(json.dumps({"status":status,"rows":rows,"size":size,"first":first,"result":out},indent=2))
 delctx(ctx)
 return status,out
if __name__=="__main__":
 seed=int(sys.argv[1]); seconds=int(sys.argv[2]); size=int(sys.argv[3]) if len(sys.argv)>3 else 19
 zero=[r for r in range(1<<N) if not target(r)]
 rows=sorted(set([1<<u|1<<v for u,v in E]+[r for r in zero if all(target(r|1<<i) for i in range(N) if not(r>>i)&1)]))
 if len(sys.argv)>4:
  if sys.argv[4]=="all": rows=list(range(1<<N))
  elif sys.argv[4]=="lower":rows=sorted(set(rows+[r for r in range(1<<N) if r.bit_count()<=2]+[1023]+[1023^(1<<i) for i in range(N)]))
  else:rows=json.loads(Path(sys.argv[4]).read_text())
 first=[(0,0,1),(0,0,2),(1,0,1),(1,0,2),(2,0,0)][seed%5]
 solve(rows,size,seconds,seed,None if N==9 else first)
