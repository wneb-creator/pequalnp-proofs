from pathlib import Path
import json, hashlib
edges=[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def f(mask): return any((mask>>a)&1 and (mask>>b)&1 for a,b in edges)
def hidden(mask): return all((mask>>a)&1 for a in [2,3,4])
def branch(mask): return bool(mask&1) or hidden(mask)
negative=[m for m in range(1<<14) if not f(m)]
maximal=[m for m in negative if all(m>>a&1 or f(m|(1<<a)) for a in range(14))]
assert len(maximal)==37
assert all(branch(m)==bool(m&1) for m in maximal)
assert all(hidden(m)==hidden(m^1) for m in range(1<<14))
assert all(not hidden(1<<a) for a in range(14))
mask=sum(1<<a for a in [2,3,4])
assert hidden(mask) and not f(mask)
result={'verdict':'PASS independent finite counterexample','scope':'Refutes the standalone inference that maximal-negative branch equality plus hidden-term independence and empty singleton support implies hidden term is contained in Fano function. This is not a 27-gate Fano circuit or a refutation of the posted gap.','x':0,'H_points':[2,3,4],'neighbor_hits':[[3,7],[2,8],[4,10]],'all_inputs_checked':16384,'maximal_negative_count':len(maximal),'maximal_negative_masks':maximal,'counterexample_mask':mask,'H_true':hidden(mask),'F_false':not f(mask),'branch_equals_x_on_all_maximal_negatives':True,'H_independent_x':True,'H_empty_singleton_support':True}
print(json.dumps(result,indent=2))
