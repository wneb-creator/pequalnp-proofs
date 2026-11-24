from itertools import combinations, combinations_with_replacement
from time import monotonic

def truth(n, edges):
    return sum(1<<bits for bits in range(1<<n) if any(bits>>a&bits>>b&1 for a,b in edges))
def cover(n,edges):
    return min(s.bit_count() for s in range(1<<n) if all((s>>a|s>>b)&1 for a,b in edges))
def girth5(n,edges):
    e={frozenset(x) for x in edges}; adj=lambda a,b:frozenset((a,b)) in e
    return all(not(adj(a,b) and adj(b,c) and adj(c,a)) for a,b,c in combinations(range(n),3)) and all(sum(adj(a,c) and adj(b,c) for c in range(n))<2 for a,b in combinations(range(n),2))
for n in [3,4]:
    started=monotonic(); mask=(1<<(1<<n))-1
    vars=[sum(1<<bits for bits in range(1<<n) if bits>>v&1) for v in range(n)]
    pairs=list(combinations(range(n),2)); targets=[]
    for b in range(1<<len(pairs)):
        e=[x for i,x in enumerate(pairs) if b>>i&1]
        if girth5(n,e): targets.append((truth(n,e),max(0,len(e)+cover(n,e)-1),e))
    for negations in [False,True]:
        initial=frozenset([0]+vars);states={initial};best={f:0 for f in initial}
        for depth in range(1,4):
            nextstates=set()
            for state in states:
                values=sorted(state);new={mask}
                if negations:new.update(mask^a for a in values)
                for a,b in combinations(values,2):new.update((a&b,a|b))
                new.difference_update(state)
                for f in new:
                    best.setdefault(f,depth)
                    nextstates.add(state|{f})
            states=nextstates
            print('n',n,'NOT',negations,'depth',depth,'states',len(states),'functions',len(best),flush=True)
        for f,bound,e in targets:
            assert best.get(f,4)>=bound,(n,negations,e,bound,best[f])
        print('n',n,'NOT',negations,'all',len(targets),'girth5targets respect m+cover-1 through3gates',flush=True)
    print('seconds',round(monotonic()-started,3),flush=True)
