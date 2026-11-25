import json
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-62')
d=json.loads((p/'packing3-blocks.json').read_text())
gs=json.loads((p/'packing-capacity3-compact-orbits.json').read_text())['inverse_generators']
rows,edges=d['rows'],d['edges']
pairs=[b[0] for b in d['blocks'][26:]]
def permute(mask,g):
 return sum(1<<g[v] for v in range(26) if mask>>v&1)
def inverse(xs):
 assert sorted(xs)==list(range(len(xs)))
 ys=[0]*len(xs)
 for i,j in enumerate(xs):ys[j]=i
 return ys
out={'vertex_permutations':gs}
for name,items in [('pair',pairs),('row',rows),('flag',edges)]:
 idx={mask:i for i,mask in enumerate(items)}
 maps=[[idx[permute(mask,g)] for mask in items] for g in gs]
 inv=[inverse(xs) for xs in maps]
 out[name+'_permutations']=maps
 out[name+'_inverse_permutations']=inv
 for g,xs,ys in zip(gs,maps,inv):
  assert all(items[xs[i]]==permute(mask,g) for i,mask in enumerate(items))
  assert all(ys[xs[i]]==i and xs[ys[i]]==i for i in range(len(items)))
 print(name,len(items),'four coordinate actions and inverse identities verified')
(p/'packing3-finite-actions.json').write_text(json.dumps(out))
