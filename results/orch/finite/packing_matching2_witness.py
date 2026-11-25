import json
from pathlib import Path
edges=[(0,1),(2,3)]
supports=[1,2,4,8,5,9,6,10]
gates=[(0,4,5),(0,6,7),(0,8,9)]
neighbors=[2,1,8,4]
for support in supports:
 assert not any((support>>a&1) and (support>>b&1) for a,b in edges)
 assert all((support & adj).bit_count()<=1 for adj in neighbors)
truth=[];dirty=[[] for _ in gates]
for point in range(16):
 values=[bool(point & support) for support in supports]
 for op,a,b in gates: values.append(values[a] and values[b])
 expected=any((point>>a&1) and (point>>b&1) for a,b in edges)
 assert values[-1]==expected
 truth.append([point,int(expected),int(values[-1])])
 if not expected:
  for j in range(3):
   if values[8+j]:dirty[j].append(point)
assert dirty[0] and dirty[1] and not dirty[2]
print(json.dumps({'graph':'matching2','edges':edges,'free_supports':supports,'paid_gates':gates,'truth_table':truth,'source_ands':[0,1],'dirty_inputs_per_and':dirty,'paid_gate_count':3,'ordinary_gate_count':7,'lower_bound_reference':'matching2-k2-packing-oracle: normalized oracle SAT query UNSAT','scope':'Counterexample to universal clean-source property for minimum paid oracle circuits, not to existential normalization, oracle cost conjecture, or L-meta-2448.'},indent=2))
