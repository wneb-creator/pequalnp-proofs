"""Retain the global archive and add independently checkable 13-AND dirty phases."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
edges = {tuple(e) for e in json.loads((HERE/'geometry.json').read_text())['edges']}
edge_masks = {(1 << a)|(1 << b) for a,b in edges}
tests = json.loads((HERE/'full-case.json').read_text())['tests'] + [[1 << i, 0] for i in range(26)]
columns = [sum((x >> i & 1) << j for j,(x,_) in enumerate(tests)) for i in range(26)]
target = sum(y << j for j,(_,y) in enumerate(tests))
guard = sum(1 << j for j,(x,_) in enumerate(tests) if x.bit_count()==1 or x in ((1<<13)-1,((1<<13)-1)<<13))
small = [0]+[1 << i for i in range(26)]+[(1<<a)|(1<<b) for a in range(26) for b in range(a+1,26) if ((1<<a)|(1<<b)) not in edge_masks]
small_columns = [sum((x >> i & 1) << j for j,x in enumerate(small)) for i in range(26)]

def normalized(terms):
    out=[]
    for term in sorted(terms,key=lambda x:(x.bit_count(),x)):
        if not any(prior&term==prior for prior in out):out.append(term)
    return frozenset(out)

def dnf(gates,replace=None):
    values=[frozenset([1<<i]) for i in range(26)]
    for i,(op,a,b) in enumerate(gates):
        values.append(values[replace[1]] if replace and replace[0]==i else normalized(values[a]|values[b] if op else {x|y for x in values[a] for y in values[b]}))
    return values

def evaluate(gates):
    assert len(gates)<=63
    values=columns.copy();small_values=small_columns.copy();dirty=0
    used={25+len(gates)}
    for i in range(len(gates)-1,-1,-1):
        if 26+i in used:used.update(gates[i][1:])
    for i,(op,a,b) in enumerate(gates):
        assert op in (0,1) and 0<=a<26+i and 0<=b<26+i
        values.append(values[a]|values[b] if op else values[a]&values[b])
        small_values.append(small_values[a]|small_values[b] if op else small_values[a]&small_values[b])
        if op==0 and a!=b and 26+i in used:dirty|=small_values[-1]
    assert values[-1]&target==target and not(values[-1]&guard)
    witness=dirty&~small_values[-1]
    return (values[-1]&~target).bit_count(), small[(witness&-witness).bit_length()-1] if witness else None

sources=[('full13_filtered',json.loads((HERE.parent/'lean_baseline/sat/full63_filtered_5extra_seed.json').read_text()))]
packet=json.loads((HERE/'six-owner-gadgets.json').read_text())[1]
for index,seed in enumerate(json.loads((HERE/'feature6-wide-validands.json').read_text())):
    if seed['ands']!=6:continue
    gates=[g.copy() for g in packet['outside_gates']]
    mapping=dict(enumerate(packet['input_original']))
    for i,f in enumerate(packet['features']):mapping[packet['raw_inputs']+i]=f['outside_wire']
    for i,(op,a,b) in enumerate(seed['gates']):
        gates.append([op,mapping[a],mapping[b]]);mapping[packet['inputs']+i]=25+len(gates)
    gates.append([1,packet['outside_output'],mapping[packet['inputs']+len(seed['gates'])-1]])
    sources.append((f'six_wide_{index}',gates))
bases=[]
for name,gates in sources:
    assert sum(op==0 and a!=b for op,a,b in gates)==13
    wrong,witness=evaluate(gates);terms=dnf(gates)
    redundant=[i for i,(op,a,b) in enumerate(gates) if op==0 and (dnf(gates,(i,a))[-1]==terms[-1] or dnf(gates,(i,b))[-1]==terms[-1])]
    live=all(any(term&edge==term for term in terms[26+i] for edge in edge_masks) for i,(op,_,_) in enumerate(gates) if op==0)
    if witness is None or redundant or not live:continue
    bases.append(dict(source=name,gates=gates,boundary_errors=wrong,suppressed_raw_mask=witness,and_count=13,dnf_terms=len(terms[-1])))
assert bases
permutations=json.loads((HERE/'global-fourteen-automorphisms.json').read_text())
added=[]
for base in bases:
    for index,perm in enumerate(permutations):
        gates=[[op,perm[a] if a<26 else a,perm[b] if b<26 else b] for op,a,b in base['gates']]
        wrong,witness=evaluate(gates);assert wrong==base['boundary_errors'] and witness is not None
        added.append(dict(source=base['source'],automorphism=index,gates=gates,boundary_errors=wrong,and_count=13))
old=json.loads((HERE/'global-fourteen-seeds.json').read_text())+json.loads((HERE/'global-fourteen-added-seeds.json').read_text())
pool=json.loads((HERE/'global14archive-pool-final.json').read_text())
champion=json.loads((HERE/'global14archive-champion-final.json').read_text())
combined=[];seen=set()
for item in [{'gates':champion}]+added+old+pool:
    gates=item['gates'];key=tuple(map(tuple,gates))
    if key in seen:continue
    seen.add(key);evaluate(gates);combined.append(item)
rows=[str(len(combined))]
for item in combined:
    rows.append(str(len(item['gates'])));rows.extend(' '.join(map(str,g)) for g in item['gates'])
(HERE/'global-min13-suppressed-seeds.txt').write_text('\n'.join(rows)+'\n')
(HERE/'global-min13-suppressed-bases.json').write_text(json.dumps(bases))
(HERE/'global-min13-suppressed-added.json').write_text(json.dumps(added))
(HERE/'global-min13-suppressed-seeds.json').write_text(json.dumps(combined))
report=dict(new13_and_bases=len(bases),new13_and_variants=len(added),retained_existing=len(old),retained_archive=len(pool),total=len(combined),best13_errors=min(b['boundary_errors'] for b in bases))
(HERE/'global-min13-suppressed-preparation.json').write_text(json.dumps(report,indent=2));print(report)
