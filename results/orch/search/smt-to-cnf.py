import argparse,ctypes,hashlib,json,time
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--input',required=True);ap.add_argument('--out',required=True);a=ap.parse_args()
src=Path(a.input).read_text();text='\n'.join(line for line in src.splitlines() if not line.startswith('(set-option') and not line.startswith('(set-logic') and not line.startswith('(check-sat'))
z=ctypes.CDLL('libz3.so.4');P=ctypes.c_void_p;U=ctypes.c_uint;B=ctypes.c_bool;S=ctypes.c_char_p
sig={'Z3_mk_config':([],P),'Z3_mk_context':([P],P),'Z3_del_config':([P],None),'Z3_del_context':([P],None),'Z3_parse_smtlib2_string':([P,S,U,P,P,U,P,P],P),'Z3_ast_vector_inc_ref':([P,P],None),'Z3_ast_vector_size':([P,P],U),'Z3_ast_vector_get':([P,P,U],P),'Z3_mk_goal':([P,B,B,B],P),'Z3_goal_inc_ref':([P,P],None),'Z3_goal_assert':([P,P,P],None),'Z3_mk_tactic':([P,S],P),'Z3_tactic_inc_ref':([P,P],None),'Z3_tactic_and_then':([P,P,P],P),'Z3_tactic_apply':([P,P,P],P),'Z3_apply_result_inc_ref':([P,P],None),'Z3_apply_result_get_num_subgoals':([P,P],U),'Z3_apply_result_get_subgoal':([P,P,U],P),'Z3_goal_to_dimacs_string':([P,P,B],S)}
for name,(args,ret) in sig.items():f=getattr(z,name);f.argtypes=args;f.restype=ret
cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg);start=time.monotonic()
v=z.Z3_parse_smtlib2_string(ctx,text.encode(),0,None,None,0,None,None);z.Z3_ast_vector_inc_ref(ctx,v)
g=z.Z3_mk_goal(ctx,False,False,False);z.Z3_goal_inc_ref(ctx,g)
for i in range(z.Z3_ast_vector_size(ctx,v)):z.Z3_goal_assert(ctx,g,z.Z3_ast_vector_get(ctx,v,i))
tac=None
for name in ['simplify','bit-blast','tseitin-cnf']:
 t=z.Z3_mk_tactic(ctx,name.encode());z.Z3_tactic_inc_ref(ctx,t)
 if tac is None:tac=t
 else:
  tac=z.Z3_tactic_and_then(ctx,tac,t);z.Z3_tactic_inc_ref(ctx,tac)
r=z.Z3_tactic_apply(ctx,tac,g);z.Z3_apply_result_inc_ref(ctx,r);count=z.Z3_apply_result_get_num_subgoals(ctx,r);assert count==1,('Expected one equivalent CNF subgoal',count)
g2=z.Z3_apply_result_get_subgoal(ctx,r,0);cnf=z.Z3_goal_to_dimacs_string(ctx,g2,True).decode();Path(a.out).write_text(cnf)
meta={'input':a.input,'input_sha256':hashlib.sha256(src.encode()).hexdigest(),'output':a.out,'cnf_sha256':hashlib.sha256(cnf.encode()).hexdigest(),'header':next(line for line in cnf.splitlines() if line.startswith('p cnf')),'bytes':len(cnf),'seconds':time.monotonic()-start,'tactics':['simplify','bit-blast','tseitin-cnf']}
Path(a.out+'.json').write_text(json.dumps(meta,indent=2));print(json.dumps(meta));z.Z3_del_context(ctx)
