import ctypes,ctypes.util,sys,time
from pathlib import Path
z=ctypes.CDLL(ctypes.util.find_library('z3'));P=ctypes.c_void_p;U=ctypes.c_uint;B=ctypes.c_bool;S=ctypes.c_char_p
specs={
'Z3_mk_config':([],P),'Z3_mk_context':([P],P),'Z3_parse_smtlib2_string':([P,S,U,P,P,U,P,P],P),
'Z3_ast_vector_inc_ref':([P,P],None),'Z3_ast_vector_size':([P,P],U),'Z3_ast_vector_get':([P,P,U],P),
'Z3_mk_goal':([P,B,B,B],P),'Z3_goal_inc_ref':([P,P],None),'Z3_goal_assert':([P,P,P],None),
'Z3_mk_tactic':([P,S],P),'Z3_tactic_inc_ref':([P,P],None),'Z3_tactic_and_then':([P,P,P],P),
'Z3_tactic_apply':([P,P,P],P),'Z3_apply_result_inc_ref':([P,P],None),'Z3_apply_result_get_num_subgoals':([P,P],U),'Z3_apply_result_get_subgoal':([P,P,U],P),
'Z3_goal_to_dimacs_string':([P,P,B],S)}
for n,(a,r) in specs.items():f=getattr(z,n);f.argtypes=a;f.restype=r
ctx=z.Z3_mk_context(z.Z3_mk_config());text=Path(sys.argv[1]).read_text()
text='\n'.join(line for line in text.splitlines() if not line.startswith('(set-option') and not line.startswith('(check-sat'))
asts=z.Z3_parse_smtlib2_string(ctx,text.encode(),0,None,None,0,None,None);z.Z3_ast_vector_inc_ref(ctx,asts)
goal=z.Z3_mk_goal(ctx,False,False,False);z.Z3_goal_inc_ref(ctx,goal)
for i in range(z.Z3_ast_vector_size(ctx,asts)):z.Z3_goal_assert(ctx,goal,z.Z3_ast_vector_get(ctx,asts,i))
tactics=[]
for name in ['simplify','propagate-values','solve-eqs','bit-blast','tseitin-cnf']:
 t=z.Z3_mk_tactic(ctx,name.encode());z.Z3_tactic_inc_ref(ctx,t);tactics.append(t)
combo=tactics[0]
for t in tactics[1:]:combo=z.Z3_tactic_and_then(ctx,combo,t);z.Z3_tactic_inc_ref(ctx,combo)
start=time.monotonic();res=z.Z3_tactic_apply(ctx,combo,goal);z.Z3_apply_result_inc_ref(ctx,res)
assert z.Z3_apply_result_get_num_subgoals(ctx,res)==1
g=z.Z3_apply_result_get_subgoal(ctx,res,0)
dimacs=z.Z3_goal_to_dimacs_string(ctx,g,False).decode();Path(sys.argv[2]).write_text(dimacs)
print('DIMACS',dimacs.splitlines()[0],'bytes',len(dimacs),'seconds',time.monotonic()-start)
