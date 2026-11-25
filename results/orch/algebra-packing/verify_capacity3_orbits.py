from itertools import combinations
from pathlib import Path
import hashlib
import json

base=Path('/tmp/oec/pequalnp-pilot-62')
data=json.loads((base/'packing-capacity3-symmetries.json').read_text())
generators=data['generators']
raw=[int(x) for x in (base/'singleton-packing-input.txt').read_text().split()]
rows=set(raw[2:470])
edges=set(raw[470:])
def act(mask,g):
    return sum(1<<g[i] for i in range(26) if mask>>i&1)
for g in generators:
    assert sorted(g)==list(range(26))
    assert {act(x,g) for x in rows}==rows
    assert {act(x,g) for x in edges}==edges
pairs=[(1<<i)|(1<<j) for i,j in combinations(range(26),2)]
pi={mask:i for i,mask in enumerate(pairs)}
lines=(base/'packing-capacity3-orbit-certificate.txt').read_text().splitlines()
assert int(lines[0])==44850 and len(lines)==44851
certificate=[tuple(map(int,line.split())) for line in lines[1:]]
states=[]
depths=[]
root_indices=[]
for index,(i,j,parent,generator) in enumerate(certificate):
    assert 0<=i<j<325 and not pairs[i]&pairs[j]
    state=(i,j)
    if parent==-1:
        assert generator==-1
        depths.append(0)
        root_indices.append(index)
    else:
        assert 0<=parent<index and 0<=generator<4
        old=states[parent]
        mapped=tuple(sorted(pi[act(pairs[k],generators[generator])] for k in old))
        assert mapped==state
        depths.append(depths[parent]+1)
    states.append(state)
expected={(i,j) for i in range(325) for j in range(i+1,325) if not pairs[i]&pairs[j]}
assert len(set(states))==44850 and set(states)==expected
assert root_indices==[r['certificate_root'] for r in data['orbits']]
small_results={}
for name,expected in [('singletons',{1<<i for i in range(26)}),('pairs',set(pairs))]:
    lines=(base/('packing-capacity3-'+name+'-certificate.txt')).read_text().splitlines()
    assert int(lines[0])==len(expected) and len(lines)==1+len(expected)
    masks=[]
    roots=[]
    for index,line in enumerate(lines[1:]):
        mask,parent,gi=map(int,line.split())
        assert mask in expected
        if parent==-1:
            assert gi==-1
            roots.append(mask)
        else:
            assert 0<=parent<index and 0<=gi<4
            assert act(masks[parent],generators[gi])==mask
        masks.append(mask)
    assert set(masks)==expected and len(set(masks))==len(expected)
    assert roots==[o['block'] for o in data[name+'_orbits']]
    small_results[name]={'states':len(masks),'roots':roots}
result={
    'status':'All concrete generator and orbit-coverage checks passed; no Lean claim.',
    'generator_count':len(generators),
    'generic_rows_preserved':len(rows),
    'incidence_edges_preserved':len(edges),
    'two_pair_states':len(states),
    'two_pair_roots':len(root_indices),
    'maximum_word_length':max(depths),
    'small_orbits':small_results,
    'simple_checker_nodes':{'two_pairs':71834,'one_pair':4393,'singletons':2455,'total':78682,'largest_root':7572},
    'certificate_sha256':hashlib.sha256((base/'packing-capacity3-orbit-certificate.txt').read_bytes()).hexdigest(),
}
print(json.dumps(result,indent=2))
(base/'packing-capacity3-orbit-verification.json').write_text(json.dumps(result,indent=2)+'\n')
