from itertools import combinations
from pathlib import Path
import json

base=Path('/tmp/oec/pequalnp-pilot-62')
data=json.loads((base/'packing-capacity3-symmetries.json').read_text())
generators=data['generators']
inverse=[]
for g in generators:
    inv=[0]*26
    for i,j in enumerate(g):inv[j]=i
    assert all(g[inv[i]]==i and inv[g[i]]==i for i in range(26))
    inverse.append(inv)
pairs=[(1<<i)|(1<<j) for i,j in combinations(range(26),2)]
pair_index={x:i for i,x in enumerate(pairs)}
def act(mask,g):return sum(1<<g[i] for i in range(26) if mask>>i&1)
inverse_pair_maps=[[pair_index[act(mask,g)] for mask in pairs] for g in inverse]
records=[list(map(int,line.split())) for line in (base/'packing-capacity3-orbit-certificate.txt').read_text().splitlines()[1:]]
depths=[]
lookup={}
roots=[]
for i,j,parent,generator in records:
    if parent==-1:
        depth=0
        generator=0
        roots.append((i,j))
    else:
        depth=1+depths[parent]
    assert 0<=depth<=10 and 0<=generator<4
    depths.append(depth)
    lookup[(i,j)]=(depth<<2)|generator
assert len(lookup)==44850
root_set=set(roots)
for (i,j),label in lookup.items():
    depth,generator=label>>2,label&3
    if depth==0:
        assert (i,j) in root_set
    else:
        inv=inverse_pair_maps[generator]
        parent=tuple(sorted((inv[i],inv[j])))
        assert parent in lookup and lookup[parent]>>2==depth-1
legal=sorted(lookup)
triangular=[(i,j) for i in range(325) for j in range(i+1,325)]
labels=[lookup[x] for x in legal]
triangle_labels=[lookup.get(x,63) for x in triangular]
def pack(xs):
    return [sum(x<<(6*j) for j,x in enumerate(xs[i:i+10])) for i in range(0,len(xs),10)]
def unpack(words,n):
    return [(words[i//10]>>(6*(i%10)))&63 for i in range(n)]
packed=pack(labels)
triangle_packed=pack(triangle_labels)
assert unpack(packed,len(labels))==labels
assert unpack(triangle_packed,len(triangle_labels))==triangle_labels
assert sum(x==63 for x in triangle_labels)==7800
for i,j in triangular:
    index=i*(649-i)//2+j-i-1
    assert triangular[index]==(i,j)
def lean_list(words):
    return '[\n'+',\n'.join('  '+', '.join(hex(x) for x in words[i:i+8]) for i in range(0,len(words),8))+'\n]\n'
(base/'packing-capacity3-compact-labels.lean.txt').write_text(lean_list(packed))
(base/'packing-capacity3-triangular-labels.lean.txt').write_text(lean_list(triangle_packed))
(base/'packing-capacity3-inverse-permutations.lean.txt').write_text('[\n'+',\n'.join('  ['+', '.join(map(str,g))+']' for g in inverse)+'\n]\n')
result={
    'label_bits':6,'labels_per_word':10,'word_bits':60,
    'legal_state_order':'lexicographic (i,j), i<j, disjoint pair masks',
    'legal_state_count':len(legal),'labels':labels,'packed_words':packed,
    'triangular_state_count':len(triangular),'triangular_index':'i*(649-i)/2+j-i-1',
    'triangular_invalid_label':63,'triangular_packed_words':triangle_packed,
    'roots':roots,'inverse_generators':inverse,'maximum_depth':max(depths),
    'verification':'Every nonroot inverse-generator step has exactly one smaller depth; depth-zero states are exactly the27roots. Packed words independently unpacked.',
}
(base/'packing-capacity3-compact-orbits.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('labels','packed_words','triangular_packed_words')},indent=2))
print('legal_lean_bytes',len((base/'packing-capacity3-compact-labels.lean.txt').read_bytes()))
print('triangular_lean_bytes',len((base/'packing-capacity3-triangular-labels.lean.txt').read_bytes()))
