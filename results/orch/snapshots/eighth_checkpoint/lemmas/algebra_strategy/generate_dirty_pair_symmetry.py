"""Exact two-orbit normalization of independent dirty inputs in the full plane."""
import itertools,json
from collections import deque,Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
residual=json.loads((HERE.parent/'verification/residual-symmetry.json').read_text())
edges={tuple(sorted((p,13+l))) for p in range(13) for l in range(13) if (p+l)%13 in (0,1,3,9)}
nonedges=set(itertools.combinations(range(26),2))-edges
assert len(edges)==52 and len(nonedges)==273
generators=[];seen=set()
def add(name,permutation):
    assert sorted(permutation)==list(range(26))
    assert {tuple(sorted((permutation[a],permutation[b]))) for a,b in edges}==edges
    key=tuple(permutation)
    if key not in seen:seen.add(key);generators.append({'name':name,'permutation':permutation})
assert residual['removed_full_input']==0
assert residual['residual_input_to_full']==list(range(1,26))
assert len(residual['permutations'])==432
for i,p in enumerate(residual['permutations']):
    add('point0_stabilizer_'+str(i),[0]+[x+1 for x in p])
for a in range(13):add('translation_'+str(a),[(p+a)%13 for p in range(13)]+[13+(l-a)%13 for l in range(13)])
add('duality',[13+p for p in range(13)]+list(range(13)))
assert len(generators)==445
index={tuple(g['permutation']):i for i,g in enumerate(generators)}
inverse_indices=[]
for g in generators:
    inverse=[0]*26
    for i,j in enumerate(g['permutation']):inverse[j]=i
    inverse_indices.append(index[tuple(inverse)])

representatives=[(0,1),(0,15)];records={};orbit_sizes=[]
for orbit,rep in enumerate(representatives):
    assert rep in nonedges
    found={rep:(list(range(26)),[])};queue=deque([rep])
    while queue:
        pair=queue.popleft();current,word=found[pair]
        for gid,g in enumerate(generators):
            p=g['permutation'];image=tuple(sorted((p[pair[0]],p[pair[1]])))
            assert image in nonedges
            if image not in found:
                found[image]=([p[current[i]] for i in range(26)],word+[gid]);queue.append(image)
    orbit_sizes.append(len(found))
    for pair,(from_rep,word) in found.items():
        assert pair not in records
        to_rep=[0]*26
        for i,j in enumerate(from_rep):to_rep[j]=i
        assert tuple(sorted((from_rep[rep[0]],from_rep[rep[1]])))==pair
        assert tuple(sorted((to_rep[pair[0]],to_rep[pair[1]])))==rep
        assert {tuple(sorted((to_rep[a],to_rep[b]))) for a,b in edges}==edges
        assert (pair[0]<13)==(pair[1]<13) if orbit==0 else (pair[0]<13)!=(pair[1]<13)
        records[pair]={'pair':list(pair),'representative':list(rep),'orbit':orbit,
            'to_representative':to_rep,'from_representative':from_rep,
            'from_representative_generator_word':word,
            'to_representative_generator_word':[inverse_indices[i] for i in reversed(word)]}
assert orbit_sizes==[156,117] and set(records)==nonedges

extensions=[]
for support in [(),*((i,) for i in range(26)),*sorted(nonedges)]:
    if not support:pair=(0,1)
    elif len(support)==1:
        v=support[0];w=(v+1)%13 if v<13 else 13+(v-13+1)%13
        pair=tuple(sorted((v,w)))
    else:pair=support
    assert set(support)<=set(pair) and pair in nonedges
    extensions.append({'support':list(support),'extension_pair':list(pair),
        'representative':records[pair]['representative'],
        'extension_pair_map_index':sorted(nonedges).index(pair)})
assert len(extensions)==300
result={'status':'Verified finite automorphism/orbit data; WLOG use additionally invokes monotonicity and input relabeling.',
        'inputs':26,'edges':[list(e) for e in sorted(edges)],'nonedge_count':273,
        'source_stabilizer':'verification/residual-symmetry.json','source_stabilizer_count':432,
        'generators':generators,'inverse_generator_indices':inverse_indices,
        'representatives':[list(x) for x in representatives],'representative_masks':[3,32769],
        'orbit_sizes':orbit_sizes,'pair_maps':[records[p] for p in sorted(nonedges)],
        'independent_support_extensions':extensions,
        'permutation_direction':'to_representative maps OLD raw vertex indices to NEW indices. Replace every raw input reference i by this permutation[i]; prior AND references stay unchanged.',
        'scope':'For a monotone circuit computing the exact posted graph function, any independent dirty support of size at most2 extends to one of the listed independent pairs. The output remains false because the extension is independent, while monotonicity preserves the dirty AND truth. A checked graph automorphism then maps the pair to one of two representatives; exact graph correctness makes the output function invariant, and input relabeling preserves gate counts. This uses no fan-in, OR-cost, or liveness assumption. The output-preservation claim is not made for arbitrary approximate circuits.'}
(HERE/'full-plane-dirty-pair-symmetry.json').write_text(json.dumps(result,indent=2)+'\n')
summary={'generators':len(generators),'edge_checks':'all445 generators and all273 pair maps',
         'orbit_sizes':orbit_sizes,'representative_masks':[3,32769],
         'all_independent_supports_size_at_most_two':len(extensions),
         'maximum_generator_word_length':max(len(r['from_representative_generator_word']) for r in records.values())}
(HERE/'full-plane-dirty-pair-symmetry-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary))
