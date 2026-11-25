import sys
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
x=z3.BitVec('conversion_probe_x',3);g=z3.Goal(models=True);g.add(x+1==3)
c=z3.Then('simplify','bit-blast','tseitin-cnf')(g)[0]
s=z3.Solver();s.add(c.as_expr());assert s.check()==z3.sat
naive=c.convert_model(s.model())
print('Z3',z3.get_version_string(),'ordinary_solver_model_entries',len(s.model()),'naive_original_assertion',naive.eval(x+1==3))
manual=z3.Model()
for clause in c:
 atom=clause.arg(0) if z3.is_not(clause) else clause
 manual.update_value(atom,z3.BoolVal(not z3.is_not(clause)))
converted=c.convert_model(manual);assert z3.is_true(converted.eval(x+1==3))
print('EXPLICIT_INTERNAL_INTERPRETATIONS_PASSED','x',converted.eval(x))
