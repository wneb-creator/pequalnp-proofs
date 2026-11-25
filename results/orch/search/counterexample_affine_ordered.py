import counterexample_affine_full as search

original_seed=search.seed
original_encoding=search.encoding

def canonical(circuit):
    n=search.NV;output=n+len(circuit)-1
    live=set();todo=[output]
    while todo:
        wire=todo.pop()
        if wire<n or wire-n in live:continue
        live.add(wire-n);op,a,b=circuit[wire-n];todo += [a,b]
    mapping={i:i for i in range(n)};pruned=[]
    for i,(op,a,b) in enumerate(circuit):
        if i in live:
            mapping[n+i]=n+len(pruned);pruned.append((op,mapping[a],mapping[b]))
    assert mapping[output]==n+len(pruned)-1
    while len(pruned)<len(circuit):
        out=n+len(pruned)-1;pruned.append((True,out,out))
    mapping={i:i for i in range(n)};remaining=set(range(len(pruned)));result=[]
    while remaining:
        ready=[(max(mapping[a],mapping[b]),min(mapping[a],mapping[b]),i)
               for i in remaining for op,a,b in [pruned[i]] if a in mapping and b in mapping]
        right,left,i=min(ready);op,_,_=pruned[i]
        mapping[n+i]=n+len(result);result.append((op,left,right));remaining.remove(i)
    assert mapping[n+len(pruned)-1]==n+len(result)-1
    assert all(result[i-1][2]<=result[i][2] for i in range(1,len(result)))
    assert search.base.evaluate(circuit,search.POS+search.NEG)==search.base.evaluate(result,search.POS+search.NEG)
    return result

def seed(rng,remove):
    circuit,details=original_seed(rng,remove)
    return canonical(circuit),dict(details,canonical_order='nondecreasing_right_operand')

def encoding(circuit):
    e=original_encoding(circuit)
    for i in range(1,len(circuit)):
        for a in range(search.NV+i-1):
            for b in range(a):e.add(-e.rhs[i-1][a],-e.rhs[i][b])
    return e

search.seed=seed
search.encoding=encoding
if __name__=='__main__':search.main()
