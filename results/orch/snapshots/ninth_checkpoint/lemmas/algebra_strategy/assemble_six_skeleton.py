"""Feature-aware assembly of raw17 AND-count skeletons for the six-owner core.

Greedy correlated-prefix substitutions are followed, when requested, by all729
compatible zero-extra outside configurations. Per-cone chunk covers are exact;
global common-OR sharing remains heuristic and is not a minimality claim.
"""
import argparse,itertools,json
from functools import lru_cache
from pathlib import Path
from assemble_encoded_and_skeleton import assemble_skeleton
import runpy
assemble_joint = runpy.run_path(str(Path(__file__).resolve().parent.parent / 'circuit_search' / 'assemble_joint_four.py'))['assemble_joint']

HERE=Path(__file__).resolve().parent

def optimize(source,case,enumerate_zero=True,max_configurations=729):
    assert source['inputs']==17 and case['inputs']==42 and case['raw_inputs']==17
    assert source.get('input_original',case['input_original'])==case['input_original']
    assert set(map(tuple,source.get('edges',case['edges'])))==set(map(tuple,case['edges']))
    k=len(source['and_gates']);features=case['features']
    feature_supports={17+i:frozenset(f['raw_indices']) for i,f in enumerate(features)}
    input_dnfs=[(1<<i,) for i in range(17)]+[tuple(1<<i for i in f['raw_indices']) for f in features]
    original=[set(g[side]) for g in source['and_gates'] for side in ('left','right')]+[set(source['output'])]
    initial=[{x if x<17 else x+25 for x in expression} for expression in original]
    def encoded(expressions):
        return {'inputs':42,'and_count':k,'and_gates':[{'left':sorted(expressions[2*i]),'right':sorted(expressions[2*i+1])} for i in range(k)],
                'output':sorted(expressions[-1]),'edges':case['edges']}
    def verify_expansion(expressions):
        for old,new in zip(original,expressions,strict=True):
            expanded=set()
            for token in new:
                if token<17:expanded.add(token)
                elif token<42:expanded.update(feature_supports[token])
                else:expanded.add(token-25)
            assert expanded==old
    seen=set();evaluations=0
    def score(expressions,final=False):
        nonlocal evaluations
        verify_expansion(expressions)
        result=assemble_skeleton(encoded(expressions),semantic=final,sharing=True,dnf_cap=20000 if final else 64,
                                 input_dnfs=input_dnfs,semantic_inputs=17)
        evaluations+=1
        if not result.get('assembled'):return None
        full,assembly=assemble_joint(case,result['gates'],result['output'])
        return (assembly['core_gates']+assembly['prefix_extra_cost'],assembly['core_gates'],len({x for gate in result['gates'] for x in gate[1:] if 17<=x<42} | ({result['output']} if 17<=result['output']<42 else set()))),result,assembly,full
    def key(expressions):return tuple(tuple(sorted(x)) for x in expressions)
    current=[x.copy() for x in initial];best=score(current);assert best is not None
    best_expressions=[x.copy() for x in current];best_origin='raw baseline';seen.add(key(current))
    steps=[]
    for step in range(100):
        candidates=[]
        for logical,support in feature_supports.items():
            changed=[x.copy() for x in current];touched=[]
            for task,expression in enumerate(changed):
                chunks={x for x in expression if (x<17 and x in support) or
                        (17<=x<42 and feature_supports[x]<=support)}
                union=set()
                for x in chunks:union.update([x] if x<17 else feature_supports[x])
                if union==set(support) and len(chunks)>=2:
                    expression.difference_update(chunks);expression.add(logical);touched.append(task)
            if not touched or key(changed) in seen:continue
            seen.add(key(changed));trial=score(changed)
            if trial is not None:candidates.append((trial[0],sum(map(len,changed)),logical,changed,trial,touched))
        if not candidates:break
        candidate=min(candidates,key=lambda x:x[:3])
        current_score=score(current)[0]
        if candidate[0][0]>current_score[0]:break
        _,_,logical,current,trial,touched=candidate
        steps.append({'feature':logical,'tasks':touched,'core_plus_extra':trial[0][0]})
        if trial[0]<best[0]:best=trial;best_expressions=[x.copy() for x in current];best_origin='greedy correlated prefixes'

    # Exact set-cover chunk count for each requested raw-line subset/configuration.
    @lru_cache(None)
    def cover(request,available):
        if not request:return ()
        chunks=[(1<<i,i) for i in range(6,17) if request>>i&1]
        chunks += [(sum(1<<i for i in feature_supports[f]),f) for f in available]
        by_bit={i:[(mask,token) for mask,token in chunks if mask>>i&1] for i in range(6,17) if request>>i&1}
        @lru_cache(None)
        def solve(remaining):
            if not remaining:return ()
            bit=(remaining&-remaining).bit_length()-1
            candidates=[tuple(sorted((token,)+solve(remaining&~mask))) for mask,token in by_bit[bit]]
            return min(candidates,key=lambda x:(len(x),x))
        return solve(request)
    configurations=0;distinct_configurations=0
    if enumerate_zero:
        groups=[[[owner['whole_input'], pair] for pair in owner['optional_inputs']] if owner['optional_inputs'] else [[owner['whole_input']]] for owner in case['outside_owners']]
        for configuration in itertools.product(*groups):
            if configurations>=max_configurations:break
            configurations+=1;available=set(itertools.chain.from_iterable(configuration));expressions=[]
            for expression in original:
                request=sum(1<<x for x in expression if 6<=x<17)
                useful=tuple(sorted(f for f in available if all(request>>i&1 for i in feature_supports[f])))
                chunks=cover(request,useful)
                expressions.append({x if x<17 else x+25 for x in expression if not 6<=x<17}|set(chunks))
            if key(expressions) in seen:continue
            seen.add(key(expressions));distinct_configurations+=1;trial=score(expressions)
            if trial is not None and trial[0]<best[0]:
                best=trial;best_expressions=[x.copy() for x in expressions];best_origin='compatible zero-extra exact per-cone covers'
    # Final full-DNF folding can improve the structurally best candidate further.
    final=score(best_expressions,True);assert final is not None
    objective,result,assembly,full=final
    N=1<<17
    columns=[int(('1'*(1<<i)+'0'*(1<<i))*(N//(2<<i)),2) for i in range(17)]
    original_values=columns[:];expected_cones=[];expected_ands=[]
    for gate in source['and_gates']:
        sides=[]
        for side in ('left','right'):
            value=0
            for x in gate[side]:value|=original_values[x]
            sides.append(value);expected_cones.append(value)
        original_values.append(sides[0]&sides[1]);expected_ands.append(original_values[-1])
    source_output=0
    for x in source['output']:source_output|=original_values[x]
    expected_cones.append(source_output)
    for f in features:
        value=0
        for i in f['raw_indices']:value|=columns[i]
        columns.append(value)
    pre=columns[:]
    for op,a,b in result['precompact_gates']:pre.append(pre[a]|pre[b] if op else pre[a]&pre[b])
    for check in result['gate_function_checks']:
        actual=0 if check['precompact_wire'] is None else pre[check['precompact_wire']]
        expected=(expected_cones if check['kind']=='OR cone' else expected_ands)[check['index']]
        assert actual==expected,check
    values=columns[:]
    for op,a,b in result['gates']:values.append(values[a]|values[b] if op else values[a]&values[b])
    actual=values[result['output']];assert actual==source_output
    target=0
    for a,b in case['edges']:target|=columns[a]&columns[b]
    return {'inputs':42,'raw_inputs':17,'gates':result['gates'],'output':result['output'],
        'and_count':result['and_count'],'or_count':result['or_count'],'assembly':assembly,
        'core_plus_prefix_extra':objective[0],'original_and_count':k,
        'optimizer_origin':best_origin,'greedy_steps':steps,'configurations_considered':configurations,
        'distinct_encoded_configurations':distinct_configurations,'assembly_evaluations':evaluations,
        'cover_cache':str(cover.cache_info()),'expanded_OR_atom_sets_verified':True,
        'all_original_gate_functions_full_truth_verified':True,'raw_assignments_checked':N,
        'false_negatives':(target&~actual).bit_count(),'false_positives':(actual&~target).bit_count(),
        'boundary_errors':[x for x,y in case['raw_tests'] if (actual>>x&1)!=y],
        'exact_core_target':actual==target,'full_candidate_within63':assembly['within_budget'],
        'full_gates':full,'encoded_skeleton':encoded(best_expressions),'dnf_assembly':result,
        'scope':'Semantics preserved on all131072 raw inputs and every original AND/cone. Per-cone covers exact; global sharing/prefix optimizer is heuristic, not a lower bound. A result is a full63 witness only if exact_core_target and full_candidate_within63 are both true.'}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('source');parser.add_argument('destination')
    parser.add_argument('--greedy-only',action='store_true');parser.add_argument('--max-configurations',type=int,default=729)
    args=parser.parse_args();source=json.loads(Path(args.source).read_text())
    case=json.loads((HERE.parent/'circuit_search'/'joint-six-owner-packet.json').read_text())[0]
    result=optimize(source,case,not args.greedy_only,args.max_configurations)
    result['source']=args.source;Path(args.destination).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['and_count','or_count','core_plus_prefix_extra','configurations_considered','distinct_encoded_configurations','assembly_evaluations','exact_core_target','full_candidate_within63','false_negatives','false_positives']}))
