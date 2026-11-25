import itertools,json,pathlib

# Nine line inputs 0,...,8 and a point/center input 9.
# Every tuple is (operation, left wire, right wire), new wires start at 10.
gates=[
 ('or',0,3),       # 10: {0,3}
 ('or',10,1),      # 11: {0,1,3}
 ('or',2,4),       # 12: {2,4}
 ('or',12,5),      # 13: {2,4,5}
 ('or',11,13),     # 14: A={0,1,2,3,4,5}
 ('or',0,6),       # 15: {0,6}
 ('or',15,1),      # 16: {0,1,6}
 ('or',2,7),       # 17: {2,7}
 ('or',17,8),      # 18: {2,7,8}
 ('or',16,18),     # 19: B={0,1,2,6,7,8}
 ('and',14,19),    # 20: singleton mask T={0,1,2}
 ('or',3,4),       # 21: {3,4}
 ('or',21,5),      # 22: {3,4,5}
 ('or',6,7),       # 23: {6,7}
 ('or',23,8),      # 24: {6,7,8}
 ('or',22,24),     # 25: E={3,4,5,6,7,8}
 ('or',20,25),     # 26: OR of all nine lines semantically
 ('and',9,26),     # 27: exact nine-leaf star
]
n=10; T={0,1,2}; P=set(range(9))
truth=[[] for _ in range(n+len(gates))]
for x in range(1<<n):
 vals=[bool(x>>i&1) for i in range(n)]
 for op,a,b in gates:
  assert a<len(vals) and b<len(vals) and a!=b
  vals.append(vals[a] and vals[b] if op=='and' else vals[a] or vals[b])
 assert vals[-1] == bool((x>>9&1) and (x&511))
 for w,v in enumerate(vals): truth[w].append(v)
masks=[{i for i in P if truth[w][1<<i]} for w in range(len(truth))]
assert masks[20]==T
aux=[w for w,M in enumerate(masks) if len(M) in (4,5) or (len(M)==2 and M<=T)]
assert aux==[]
below=[all(not a or b for a,b in zip(ts,truth[-1])) for ts in truth]
assert below[-1]
assert not any(below[:-1])
for j,(op,a,b) in enumerate(gates):
 if op=='or': assert below[a]==below[b]
 if op=='and': assert not below[a] and not below[b]
 assert any(truth[n+j][(1<<9)|(1<<i)] for i in P)
seen={n+len(gates)-1}
for j in reversed(range(len(gates))):
 if n+j in seen: seen.update(gates[j][1:])
assert set(range(n,n+len(gates)))<=seen
report=dict(inputs=n,point=9,lines=list(range(9)),gates=gates,output=27,
 singleton_masks=[sorted(x) for x in masks],target_triple=sorted(T),auxiliary_wires=aux,
 checked_assignments=1<<n,exact_star=True,normalized=True,all_gates_edge_visible=True,
 all_gates_structurally_live=True,size=len(gates),star_optimum=9)
pathlib.Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS: 1024 assignments; exact 9-leaf star; normalized; edge-visible; live; Aux empty; 18 gates')
