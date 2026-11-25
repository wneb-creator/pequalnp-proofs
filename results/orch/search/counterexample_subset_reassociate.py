import counterexample_subset_corephase as c
s=c.s
original=c.coreseed


def seed(rng,roots=7,control=False):
    circuit,details=original(rng,roots,control)
    mode=rng.randrange(3);details['association_mode']=mode
    if mode==0:return circuit,details
    dirty=len(circuit)-(2*roots-1)
    ands=[i for i,(op,_,_) in enumerate(circuit[:dirty]) if op]
    assert len(ands)==1;i=ands[0];g=s.NV+i
    parents=[j for j in range(dirty,dirty+roots) if g in circuit[j][1:]]
    assert len(parents)==1;j=parents[0]
    _,a,b=circuit[i];keep,drop=(a,b) if mode==1 else (b,a)
    _,left,right=circuit[j];neighbor=right if left==g else left
    modified=list(circuit);modified[i]=(True,keep,neighbor);modified[j]=(True,g,drop)
    mapping={v:v for v in range(s.NV)};ordered=[];pending=set(range(dirty))
    while pending:
        ready=[k for k in pending if all(w in mapping for w in modified[k][1:])]
        assert ready
        k=min(ready,key=lambda k:(max(mapping[w] for w in modified[k][1:]),min(mapping[w] for w in modified[k][1:]),k))
        op,x,y=modified[k];x,y=sorted((mapping[x],mapping[y]))
        mapping[s.NV+k]=s.NV+len(ordered);ordered.append((op,x,y));pending.remove(k)
    rootargs=[tuple(sorted((mapping[x],mapping[y]))) for _,x,y in modified[dirty:dirty+roots]]
    rootargs.sort(key=lambda p:(p[1],p[0]));result=ordered+[(True,x,y) for x,y in rootargs]
    output=s.NV+dirty
    for k in range(1,roots):
        result.append((False,output,s.NV+dirty+k));output=s.NV+len(result)-1
    assert len(result)==len(circuit)
    assert s.base.evaluate(result,s.POS+s.NEG)==s.base.evaluate(circuit,s.POS+s.NEG)
    if control:c.r.verify(result,roots)
    details['phase_family']+='_reassociated'
    return result,details


def main():
    c.coreseed=seed;c.main()

if __name__=='__main__':main()
