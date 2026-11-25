from pathlib import Path
import json

scratch=Path('/tmp/oec/pequalnp-pilot-93')
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
clauses=[[1,3,7],[0,3,9],[0,7,8],[1,8,9]]
centers=[2,4,5,6]
matching=[(0,1),(3,8),(7,9)]
wvars=[0,1,3,7,8,9]
seed=[tuple(map(int,line.split())) for line in (scratch/'window_seed.txt').read_text().splitlines()]
assert seed[0]==(2,10,10)
gates=[]
for op,a,b in seed[1:]:
    assert op in (0,1) and a!=10 and b!=10
    gates.append((op,a-(a>10),b-(b>10)))
assert len(gates)==18
tables=[[] for _ in range(28)]
error_rows=[]
for row in range(1024):
    wires=[bool(row>>k&1) for k in range(10)]
    ys=[any(wires[k] for k in clause) for clause in clauses]
    b=any(wires[c] and y for c,y in zip(centers,ys))
    q=all(ys)
    m=any(wires[a] and wires[b] for a,b in matching)
    expected=any(wires[a] and wires[b] for a,b in edges)
    assert expected==(b or m)
    for op,a,c in gates:
        wires.append(wires[a]&wires[c] if op==0 else wires[a]|wires[c])
    assert wires[-1]==(b or q)
    for k,value in enumerate(wires):
        tables[k].append(value)
    if wires[-1]!=expected:
        assert not expected
        error_rows.append(row)
assert set(error_rows)=={sum(1<<k for k in clause) for clause in clauses}
for row in error_rows:
    for k in range(10):
        if not row>>k&1:
            sup=row|(1<<k)
            assert any(sup>>a&sup>>b&1 for a,b in edges)
wrows=[sum((mask>>i&1)<<k for i,k in enumerate(wvars)) for mask in range(64)]
restricted=[sum(int(table[row])<<mask for mask,row in enumerate(wrows)) for table in tables]
mtable=sum(int(any(row>>a&row>>b&1 for a,b in matching))<<mask for mask,row in enumerate(wrows))
qtable=restricted[-1]
etable=qtable & ~mtable
assert etable.bit_count()==4 and mtable.bit_count()==37
masking_wires=[k for k,t in enumerate(restricted) if t&etable==etable]
assert all(t&mtable==mtable for k,t in enumerate(restricted) if k in masking_wires)
valid_existing=[k for k,t in enumerate(restricted) if t and not t&~mtable]
assert not valid_existing
edge_rows=[sum(1<<k for k in pair) for pair in matching]
edge_masks=[wrows.index(row) for row in edge_rows]
valid_one_gate=[]
for a,ta in enumerate(restricted):
    for b in range(a,len(restricted)):
        tb=restricted[b]
        for op,t in [('and',ta&tb),('or',ta|tb)]:
            if t and not t&~mtable:
                valid_one_gate.append({'op':op,'inputs':[a,b],'matching_edges_covered':[matching[j] for j,r in enumerate(edge_masks) if t>>r&1],'table':t})
assert all(entry['table']!=mtable for entry in valid_one_gate)

edge_set={tuple(sorted(e)) for e in edges}
def adjacent(a,b):return tuple(sorted((a,b))) in edge_set
autos=[]
def visit(images):
    if len(images)==10:
        autos.append(images)
        return
    i=len(images)
    for j in range(10):
        if j not in images and all(adjacent(i,k)==adjacent(j,images[k]) for k in range(i)):
            visit(images+[j])
visit([])
ordered_edges={(p[0],p[1]) for p in autos}
ordered_nonedges={(p[0],p[2]) for p in autos}
assert ordered_edges=={(a,b) for a in range(10) for b in range(10) if adjacent(a,b)}
assert ordered_nonedges=={(a,b) for a in range(10) for b in range(10) if a!=b and not adjacent(a,b)}
result={'scope':'Exact finite Python computations and stated algebraic consequences; not yet Lean formalization.','gates':gates,'output':27,'verified_rows':1024,'centers':centers,'neighbor_or_clauses':clauses,'matching':matching,'factorization':'near = B OR Q; Petersen = B OR M; B = OR_i(center_i AND Y_i); Q = AND_i Y_i','error_rows':error_rows,'error_triples':clauses,'each_error_is_maximal_independent':True,'restriction':'Set the four center inputs to false; then B=false, near=Q, target=M.','matching_true_rows_on_six_inputs':mtable.bit_count(),'wrong_rows_on_six_inputs':etable.bit_count(),'existing_wires_true_on_all_errors':masking_wires,'every_such_wire_true_on_all_matching_inputs':True,'nonzero_existing_wires_implying_matching':valid_existing,'valid_positive_one_gate_rescues':valid_one_gate,'one_gate_cannot_compute_entire_matching':True,'ordered_pair_symmetry':{'automorphisms':len(autos),'edge_orbit_size':len(ordered_edges),'nonedge_orbit_size':len(ordered_nonedges)}}
(scratch/'near-symbolic-analysis.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
