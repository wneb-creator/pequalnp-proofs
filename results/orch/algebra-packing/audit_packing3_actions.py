import ast
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

base=Path('/tmp/oec/pequalnp-pilot-62')
repo=Path('/workspace/pequalnp-proofs')
actions=json.loads((base/'packing3-finite-actions.json').read_text())
blocks=json.loads((base/'packing3-blocks.json').read_text())
compact=json.loads((base/'packing-capacity3-compact-orbits.json').read_text())
raw=[int(x) for x in (base/'singleton-packing-input.txt').read_text().split()]
rows=raw[2:470]
old_edges=raw[470:]
edges=[(1<<((l+d)%13))|(1<<(13+l)) for l in range(13) for d in (0,1,3,9)]
pairs=[(1<<i)|(1<<j) for i,j in combinations(range(26),2)]
def numeric_list(text,start):
    begin=text.index('[',start)
    depth=0
    for i in range(begin,len(text)):
        if text[i]=='[':depth+=1
        elif text[i]==']':
            depth-=1
            if not depth:return ast.literal_eval(text[begin:i+1])
    raise AssertionError('unclosed numeric list')
all_rows=(repo/'results/orch/lemmas/AllRows.lean').read_text()
literal_rows=numeric_list(all_rows,all_rows.index('def row ('))
assert len(literal_rows)==36 and all(len(group)==13 for group in literal_rows)
lean_rows=[sum(1<<v for v in row) for group in literal_rows for row in group]
assert lean_rows==rows==blocks['rows']
flags=(repo/'results/orch/lemmas/FlagDeletion.lean').read_text()
literal_flags=numeric_list(flags,flags.index('def flag ('))
assert literal_flags==[((l+d)%13,l) for l in range(13) for d in (0,1,3,9)]
assert edges==blocks['edges']
assert [b[0] for b in blocks['blocks'][26:]]==pairs
assert actions['vertex_permutations']==compact['inverse_generators']
def permute(mask,g):return sum(1<<g[v] for v in range(26) if mask>>v&1)
counts={}
for name,items in [('pair',pairs),('row',rows),('flag',edges)]:
    maps=actions[name+'_permutations']
    inverses=actions[name+'_inverse_permutations']
    assert len(maps)==len(inverses)==4
    for g,p,inv in zip(actions['vertex_permutations'],maps,inverses):
        assert sorted(g)==list(range(26))
        assert sorted(p)==sorted(inv)==list(range(len(items)))
        assert all(items[p[i]]==permute(mask,g) for i,mask in enumerate(items))
        assert all(inv[p[i]]==i and p[inv[i]]==i for i in range(len(items)))
    counts[name]=len(items)*4
old_index={e:i for i,e in enumerate(old_edges)}
new_index={e:i for i,e in enumerate(edges)}
old_to_new=[new_index[e] for e in old_edges]
new_to_old=[old_index[e] for e in edges]
assert all(new_to_old[old_to_new[i]]==i for i in range(52))
result={
    'status':'Independent exact-array audit passed.',
    'actions_sha256':sha256((base/'packing3-finite-actions.json').read_bytes()).hexdigest(),
    'coordinate_generators':'Exactly the previously verified inverse generators.',
    'row_order':'Matches the 36-by-13 AllRows.row literal and original input exactly.',
    'flag_order':'Matches Flags.flag: line-major, offsets0,1,3,9 before modular wrap.',
    'checked_coordinate_set_images':counts,
    'all_index_maps_and_inverse_maps_are_bijections':True,
    'old_edge_order_to_Flags_order':old_to_new,
    'Flags_order_to_old_edge_order':new_to_old,
}
print(json.dumps(result,indent=2))
(base/'packing3-actions-independent-audit.json').write_text(json.dumps(result,indent=2)+'\n')
