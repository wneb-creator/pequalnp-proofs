import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
c=json.loads((HERE/'five_owner_pair_extension_census.json').read_text())
raw=c['input_original']; negatives=c['negative_masks']
geometry=json.loads((HERE.parent/'circuit_search/geometry.json').read_text())
edges={tuple(sorted((raw.index(u),raw.index(v)))) for u,v in geometry['edges'] if u in c['rows']}
dirty={tuple(x['local']) for x in c['five_and_dirty_pair_exceptions']}
allowed=edges|dirty
adj=[sum(1<<v for v in range(16) if tuple(sorted((u,v))) in allowed and u!=v) for u in range(16)]
records=[]; maximum=0; checked=0
for left in range(1,1<<16):
    common=65535
    for i in range(16):
        if left>>i&1: common &= adj[i]
    upper=sum(bool(((left>>a&1) and (common>>b&1)) or ((left>>b&1) and (common>>a&1))) for a,b in edges)
    if upper<4: continue
    right=common
    while right:
        if left<right:
            checked+=1
            count=sum(bool(((left>>a&1) and (right>>b&1)) or ((left>>b&1) and (right>>a&1))) for a,b in edges)
            if count>=4:
                negative_true=sum(bool(U&left) and bool(U&right) for U in negatives)
                if negative_true<=2:
                    maximum=max(maximum,count)
                    records.append({'left':[i for i in range(16) if left>>i&1],
                                    'right':[i for i in range(16) if right>>i&1],
                                    'positive_edges':count,'negative_true_count':negative_true})
        right=(right-1)&common
result={'claim_scope':'All raw singleton-support rectangles compatible with singleton exclusion, every individually forbidden dirty pair excluded, and at most2 maximal negatives activated. This checks only true11 negative states; it does not require forced-active or zero00 conditions. Rectangles with fewer than4 target edges are omitted.',
        'checked_candidate_right_subsets':checked,'max_positive_edges':maximum,
        'rectangles_with_at_least_four_edges':records}
assert maximum==4 and len(records)==9 and checked==127
text=json.dumps(result,indent=2)+'\n'
assert (HERE/'five_owner_all_and_rectangles.json').read_text()==text
witnesses=[]
for index,r in enumerate(records):
    if not r['negative_true_count']: continue
    left=sum(1<<i for i in r['left']);right=sum(1<<i for i in r['right'])
    bad=[U for U in negatives if U&left and U&right]
    owner=next(i for i in r['left']+r['right'] if i<5)
    assert len(bad)==2
    guards=[]
    for j in range(5):
        if j==owner:continue
        neighbors={v for u,v in edges if u==j}
        U=next(U for U in bad if not(U>>j&1))
        line=next(v for v in sorted(neighbors) if U>>v&1)
        guards.append({'other_owner':j,'negative_mask':U,'true_neighbor':line})
    witnesses.append({'rectangle_index':index,'owner':owner,'bad_maximal_negatives':bad,
                      'bad_negative_owner_sets':[[j for j in range(5) if U>>j&1] for U in bad],
                      'other_owner_absence_witnesses':guards})
(HERE/'five_owner_dirty_hub_witnesses.json').write_text(json.dumps(witnesses,indent=2)+'\n')
print('Reproduced all9 maximal4-edge rectangles from65535 left subsets and127 viable right subsets; generated16 dirty-hub filtering witnesses.')
