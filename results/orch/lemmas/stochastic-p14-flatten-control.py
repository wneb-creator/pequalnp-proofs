from pathlib import Path
from collections import Counter
import json,sys,hashlib
base=Path(sys.argv[1]);n=14;g=[]
def gate(op,a,b):
    assert a!=b and 0<=a<n+len(g) and 0<=b<n+len(g)
    g.append([op,a,b]);return n+len(g)-1
q=gate('and',0,1);px=gate('or',6,q);r=gate('and',px,2);s=gate('and',px,3)
py=gate('or',7,r);u=gate('and',py,4);v=gate('and',py,5)
terms=[s,u,v,gate('and',0,1),gate('and',2,3),gate('and',4,5)]
for a,b in [(8,9),(9,10),(10,11),(11,12),(12,13),(13,8)]:terms.append(gate('and',a,b))
out=terms[0]
for t in terms[1:]:out=gate('or',out,t)
assert len(g)==27
fan=Counter(a for _,a,b in g)+Counter(b for _,a,b in g)
support=[{i} for i in range(n)]
for op,a,b in g:support.append(support[a]&support[b] if op=='and' else support[a]|support[b])
branch=[w for w in range(out) if fan[w]>=2]
assert len(branch)==14 and all(fan[w]==2 and len(support[w])==1 for w in branch)
assert Counter(next(iter(support[w])) for w in branch)==Counter(range(n))
assert not support[out]
assert all(not support[n+j] and fan[n+j]==1 for j,(op,a,b) in enumerate(g) if op=='and')
assert all(not(support[a]&support[b]) for op,a,b in g if op=='or')
and_wires=[n+j for j,(op,a,b) in enumerate(g) if op=='and'];ids={w:j for j,w in enumerate(and_wires)}
flat={i:({i},set()) for i in range(n)};ands=[]
for j,(op,a,b) in enumerate(g):
    w=n+j
    if op=='and':
        ands.append([{'S':sorted(flat[a][0]),'T':sorted(flat[a][1])},{'S':sorted(flat[b][0]),'T':sorted(flat[b][1])}])
        flat[w]=(set(),{ids[w]})
    else:flat[w]=(flat[a][0]|flat[b][0],flat[a][1]|flat[b][1])
slots=[slot for pair in ands for slot in pair];output={'S':sorted(flat[out][0]),'T':sorted(flat[out][1])}
sc=Counter(x for slot in slots for x in slot['S']);assert all(sc[x]==2 for x in range(n))
occ={a:[j for j,slot in enumerate(slots+[output]) if a in slot['T']] for a in range(len(ands))}
owners={}
for a,uses in occ.items():
    assert 1<=len(uses)<=2
    if len(uses)==2:
        assert max(uses)<len(slots)
        common=set(slots[uses[0]]['S'])&set(slots[uses[1]]['S'])
        assert len(common)==1
        owners[a]=next(iter(common))
for j,pair in enumerate(ands):
    assert not(set(pair[0]['S'])&set(pair[1]['S']))
    assert all(a<j for slot in pair for a in slot['T'])
# Independent full Boolean row comparison of DAG and flattened expressions.
for row in range(1<<n):
    vals=[bool(row>>i&1) for i in range(n)]
    for op,a,b in g:vals.append(vals[a] and vals[b] if op=='and' else vals[a] or vals[b])
    av=[]
    def operand(slot):return any(row>>i&1 for i in slot['S']) or any(av[a] for a in slot['T'])
    for pair in ands:av.append(operand(pair[0]) and operand(pair[1]))
    assert vals[out]==operand(output)
# Count recursive occurrences of the first AND node, stopping only at that node.
counts=[]
for w in range(n+len(g)):
    if w<n:counts.append(0)
    elif w==q:counts.append(1)
    else:_,a,b=g[w-n];counts.append(counts[a]+counts[b])
assert counts[out]==3 and len(occ[ids[q]])==2
control={'scope':'Structural equality-model positivecontrol ONLY. This is not the Fano function and not a gap witness. Recursive expansion of the first AND atom occurs3times; direct OR-only flattening has2 occurrences.','n_inputs':n,'size':len(g),'gates':g,'output':out,'AND_count':len(ands),'OR_count':len(g)-len(ands),'all_inputs_eligible':True,'Bzero':0,'totalSurplus':sum(max(0,fan[w]-1) for w in range(out)),'all_AND_outputs_empty_support':True,'all_AND_outputs_fanout_one':True,'one_pure_branch_per_label':True,'no_OR_carrier_merges':True,'recursive_Q_occurrences':counts[out],'direct_Q_occurrences':len(occ[ids[q]]),'not_Fano_witness_row':3}
compact={'ANDs':ands,'output':output,'repeated_atom_owners':owners,'primary_occurrences':dict(sc),'atom_occurrence_slots':occ}
(base/'stochastic-p14-flatten-control.json').write_text(json.dumps(control,indent=2)+'\n')
(base/'stochastic-p14-flatten-compact.json').write_text(json.dumps(compact,indent=2)+'\n')
print(json.dumps({k:v for k,v in control.items() if k not in ['gates','scope']}))
