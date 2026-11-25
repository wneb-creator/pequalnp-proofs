"""Exact outside-prefix synthesis and assembly for the five-owner packet."""
from functools import lru_cache
from itertools import combinations

@lru_cache(None)
def or_network_table(arity):
    composite=sorted((m for m in range(1,1<<arity) if m.bit_count()>=2),key=lambda m:(m.bit_count(),m))
    index={m:i for i,m in enumerate(composite)}
    parent={0:None};queue=[0]
    for state in queue:
        available=[1<<i for i in range(arity)]+[m for i,m in enumerate(composite) if state>>i&1]
        for a,b in combinations(available,2):
            union=a|b
            if union==a or union==b or state>>index[union]&1:continue
            nxt=state|1<<index[union]
            if nxt not in parent:parent[nxt]=(state,a,b,union);queue.append(nxt)
    best=[state if state in parent else None for state in range(1<<len(composite))]
    for bit in range(len(composite)):
        for state in range(len(best)):
            if state>>bit&1:continue
            other=best[state|1<<bit]
            if other is not None and (best[state] is None or other.bit_count()<best[state].bit_count()):best[state]=other
    return composite,index,parent,best

def or_network(arity,required):
    composite,index,parent,best=or_network_table(arity)
    request=sum(1<<index[m] for m in set(required))
    state=best[request];network=[]
    while state:
        previous,a,b,union=parent[state];network.append((a,b,union));state=previous
    return network[::-1]

def compact_core(inputs,gates,output=None):
    output=inputs+len(gates)-1 if output is None else output
    mapping={i:i for i in range(inputs)};made=[];cache={}
    for i,(op,a,b) in enumerate(gates):
        assert op in (0,1) and 0<=a<inputs+i and 0<=b<inputs+i
        a,b=sorted((mapping[a],mapping[b]));key=(op,a,b)
        if a==b:mapping[inputs+i]=a
        else:
            if key not in cache:cache[key]=inputs+len(made);made.append(list(key))
            mapping[inputs+i]=cache[key]
    output=mapping[output];used={output}
    for i in range(len(made)-1,-1,-1):
        if inputs+i in used:used.update(made[i][1:])
    ren={i:i for i in range(inputs)};core=[]
    for i,(op,a,b) in enumerate(made):
        if inputs+i in used:ren[inputs+i]=inputs+len(core);core.append([op,ren[a],ren[b]])
    return core,ren[output],{i for i in used if i<inputs}

def assemble_five(case,gates,output=None):
    core,output,used=compact_core(case['inputs'],gates,output)
    made=[];mapping={i:x for i,x in enumerate(case['input_original'])};extra=0
    def gate(op,a,b):made.append([op,a,b]);return 25+len(made)
    wholes={}
    for owner in case['outside_owners']:
        lines=owner['core_lines'];arity=len(lines);whole=(1<<arity)-1
        required={whole}
        for feature_input in owner['feature_inputs']:
            if feature_input in used:required.add(case['features'][feature_input-case['raw_inputs']]['local_mask'])
        network=or_network(arity,required);extra+=len(network)-(arity-1)
        local={1<<i:x for i,x in enumerate(lines)}
        for a,b,union in network:local[union]=gate(1,local[a],local[b])
        for feature_input in owner['feature_inputs']:
            mask=case['features'][feature_input-case['raw_inputs']]['local_mask']
            if mask in local:mapping[feature_input]=local[mask]
        wholes[owner['outside_point']]=local[whole]
    terms=[]
    for owner in case['outside_owners']:
        w=wholes[owner['outside_point']]
        for line in owner['original_neighbors']:
            if line not in owner['core_lines']:w=gate(1,w,line)
        terms.append(gate(0,owner['outside_point'],w))
    outside=terms[0]
    for term in terms[1:]:outside=gate(1,outside,term)
    outside_cost=len(made);assert outside_cost==39+extra
    for i,(op,a,b) in enumerate(core):mapping[case['inputs']+i]=gate(op,mapping[a],mapping[b])
    gate(1,outside,mapping[output])
    return made,{'core_gates':len(core),'outside_gates':outside_cost,'prefix_extra_cost':extra,
                 'gates':len(made),'within_budget':len(made)<=63,'used_features':sorted(i for i in used if i>=case['raw_inputs'])}
