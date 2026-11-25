import json
from pathlib import Path
from itertools import combinations

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent / 'circuit_search/joint-six-owner-packet.json'
packet = json.loads(PACKET.read_text())
assert isinstance(packet, list) and len(packet) == 1 and isinstance(packet[0], dict)
case = packet[0]
raw = case['input_original']
assert len(raw) == case['raw_inputs'] == 17 and len(case['group']) == 6
assert raw[:6] == case['group']
edges = {tuple(edge) for edge in case['edges']}
assert len(edges) == 24 and all(0 <= a < 6 <= b < 17 for a,b in edges)
neighborhoods = [sum(1 << (b-6) for a,b in edges if a == p) for p in range(6)]
counts = {}
negative_masks = {}
for retained in range(2048):
    unions = {0}
    for neighbors in neighborhoods:
        unions |= {u | (neighbors & retained) for u in unions}
    counts[retained] = len(unions)
    if retained == 2047:
        negative_masks = sorted(
            sum(1 << p for p,neighbors in enumerate(neighborhoods)
                if (neighbors & retained) | neighbors_union == neighbors_union)
            | ((retained ^ neighbors_union) << 6)
            for neighbors_union in unions)
assert counts[2047] == len(negative_masks) == 52
assert negative_masks == sorted(mask for mask,label in case['raw_tests'] if not label)
for i,U in enumerate(negative_masks):
    assert not any((U>>a&1) and (U>>b&1) for a,b in edges)
    for V in negative_masks[i+1:]:
        both = U | V
        assert any((both>>a&1) and (both>>b&1) for a,b in edges)
minimal = [mask for mask,count in counts.items() if count > 32 and
           all(counts[mask ^ (1<<j)] <= 32 for j in range(11) if mask>>j&1)]
assignments = []
for mask in minimal:
    value = 63 | (mask << 6)
    encoded = value
    for j,feature in enumerate(case['features'],17):
        if any(value>>i&1 for i in feature['raw_indices']):
            encoded |= 1<<j
    assignments.append({'raw_mask':value,'encoded_mask':encoded,
                        'retained_line_original':[raw[6+j] for j in range(11) if mask>>j&1],
                        'restricted_maximal_negatives':counts[mask]})
pairs=[]
for a,b in combinations(range(17),2):
    if (a,b) in edges or (b,a) in edges:
        continue
    pair=(1<<a)|(1<<b)
    multiplicity=sum(U&pair==pair for U in negative_masks)
    pairs.append({'local':[a,b],'original':[raw[a],raw[b]],
                  'maximal_negative_extensions':multiplicity,
                  'all_ANDs_must_be_false_with_six_ANDs':multiplicity>12})
singletons=[{'local':i,'original':raw[i],
             'maximal_negative_extensions':sum(bool(U>>i&1) for U in negative_masks)}
            for i in range(17)]
result = {
    'packet':str(PACKET.relative_to(HERE.parent)), 'input_original':raw,
    'raw_inputs':17,'encoded_inputs':case['inputs'],'rows':case['group'],
    'edges':sorted(map(list,edges)), 'maximal_negative_masks':negative_masks,
    'maximal_negative_count':52,'exact_AND_count':6,'weighted_Kraft_slack':12,
    'forced_active_scope':'Any exact core with at most6 binary ANDs and pure-OR features has every AND true at each listed upper assignment: the restricted graph has more than32 maximal negatives, so a false AND could be replaced by false OR on the downset, contradicting the5-AND family bound. Generic ForcedActiveAnd.lean proves the rule; concrete counts here are computational data.',
    'forced_active_minimal_count':len(assignments),'forced_active_assignments':assignments,
    'retained_line_count_histogram':{str(k):sum(m.bit_count()==k for m in minimal) for k in sorted({m.bit_count() for m in minimal})},
    'restricted_negative_count_histogram':{str(k):sum(c==k for c in counts.values()) for k in sorted(set(counts.values()))},
    'pair_scope':'For an exact6-AND core, sum2^equal_operand_count over52 maximal negatives is at most64. Any independent pair in more than12 maxima therefore makes everyAND false by monotonicity. Pairs with at most12 extensions are only candidates, not guaranteed realizable dirty inputs.',
    'independent_pair_census':pairs,'singleton_census':singletons,
    'forbidden_dirty_pair_count':sum(x['all_ANDs_must_be_false_with_six_ANDs'] for x in pairs),
    'possible_dirty_pair_count':sum(not x['all_ANDs_must_be_false_with_six_ANDs'] for x in pairs),
}
output=HERE/'joint_six_restriction_census.json'
output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['rows','maximal_negative_count','forced_active_minimal_count','retained_line_count_histogram','forbidden_dirty_pair_count','possible_dirty_pair_count']},indent=2))
print('singleton extension range',min(x['maximal_negative_extensions'] for x in singletons),max(x['maximal_negative_extensions'] for x in singletons))
print('pair extension range',min(x['maximal_negative_extensions'] for x in pairs),max(x['maximal_negative_extensions'] for x in pairs))
