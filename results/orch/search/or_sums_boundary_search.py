import argparse
import json
import math
import random
import time
from pathlib import Path

N=13
D={0,1,3,9}
MASK=(1<<N)-1
SETS=[sum(1<<l for l in range(N) if (p-l)%N in D) for p in range(N)]
SAMPLES=[1<<i for i in range(N)]+[MASK^s for s in SETS]
INPUTS=[sum(((x>>i)&1)<<j for j,x in enumerate(SAMPLES)) for i in range(N)]
CACHE={}


def costs(v):
    try:return CACHE[v]
    except KeyError:pass
    c=tuple(((~v)&s).bit_count()+6*((v>>(N+j))&1) for j,s in enumerate(SETS))
    if len(CACHE)>200000:CACHE.clear()
    CACHE[v]=c
    return c


def evaluate(gates):
    wires=INPUTS.copy()
    for op,a,b in gates:
        wires.append(wires[a]|wires[b] if op==0 else wires[a]&wires[b])
    best=[100]*N
    outputs=[-1]*N
    for i,v in enumerate(wires):
        c=costs(v)
        for j in range(N):
            if c[j]<best[j]:best[j],outputs[j]=c[j],i
    return sum(best),sum(x!=0 for x in best),tuple(outputs),tuple(best)


def remove(gates,j,side):
    dead=N+j
    repl=gates[j][side]
    def ren(i):
        if i==dead:return repl
        return i-1 if i>dead else i
    result=[]
    for k,(op,a,b) in enumerate(gates):
        if k==j:continue
        a,b=ren(a),ren(b)
        if a==b:b=(a+1)%(N+len(result))
        result.append((op,min(a,b),max(a,b)))
    return tuple(result)


def seed(rng):
    gates=[]
    rows=list(range(N));rng.shuffle(rows)
    for p in rows:
        nodes=[i for i in range(N) if (SETS[p]>>i)&1]
        while len(nodes)>1:
            a=nodes.pop(rng.randrange(len(nodes)))
            b=nodes.pop(rng.randrange(len(nodes)))
            gates.append((0,min(a,b),max(a,b)))
            nodes.append(N+len(gates)-1)
    return remove(gates,rng.randrange(39),rng.choice([1,2]))


def mutate(gs,rng):
    gates=list(gs)
    for _ in range(rng.choices([1,2,3,5],[80,15,4,1])[0]):
        j=rng.randrange(len(gates));op,a,b=gates[j]
        kind=rng.randrange(12)
        if kind<2:op^=1
        elif kind==2:
            a,b=rng.sample(range(N+j),2)
            op=rng.randrange(2)
        elif kind==3 and j>0:
            # Copy a useful earlier gate's operation/operands into this slot.
            op,a,b=gates[rng.randrange(j)]
        else:
            if rng.randrange(2):a=rng.randrange(N+j)
            else:b=rng.randrange(N+j)
        if a==b:b=(a+1)%(N+j)
        gates[j]=(op,min(a,b),max(a,b))
    return tuple(gates)


def verify(gates,outputs):
    for mask in range(1<<N):
        w=[bool((mask>>i)&1) for i in range(N)]
        for op,a,b in gates:
            assert a!=b and max(a,b)<len(w)
            w.append((w[a] or w[b]) if op==0 else (w[a] and w[b]))
        assert all(w[outputs[j]]==bool(mask&SETS[j]) for j in range(N))


def run(seconds,rngseed,out):
    rng=random.Random(rngseed)
    begun=time.monotonic()
    chains=[]
    for k in range(24):
        gs=seed(rng);chains.append([gs,evaluate(gs),[0,0.1,0.25,0.5,0.8,1.2][k%6],0])
    best=(10000,10000)
    iterations=0;accepted=0;reports=time.monotonic()+30
    while time.monotonic()-begun<seconds:
        iterations+=1
        chain=rng.choice(chains)
        gs=mutate(chain[0],rng)
        f=evaluate(gs)
        obj=(f[0],f[1])
        if obj<best:
            best=obj
            payload=dict(seed=rngseed,seconds=time.monotonic()-begun,iterations=iterations,
                         score=f[0],incorrect_outputs=f[1],gates=gs,outputs=f[2],per_output_costs=f[3],
                         basis='13 singleton inputs and13 complements of required4-subsets')
            out.write_text(json.dumps(payload)+'\n')
            print(json.dumps({k:v for k,v in payload.items() if k not in ['gates','outputs']}),flush=True)
        if f[0]==0:
            verify(gs,f[2])
            print(json.dumps(dict(found=True,verified_all_8192_inputs=True,iterations=iterations)),flush=True)
            return
        delta=f[0]-chain[1][0]
        if delta<=0 or (chain[2]>0 and rng.random()<math.exp(-delta/chain[2])):
            chain[0],chain[1]=gs,f;accepted+=1
        chain[3]+=1
        if chain[3]>20000:
            gs=seed(rng);chain[0],chain[1],chain[3]=gs,evaluate(gs),0
        if time.monotonic()>reports:
            print(json.dumps(dict(progress=True,iterations=iterations,accepted=accepted,best=best,
                                  seconds=time.monotonic()-begun,seed=rngseed,cache_size=len(CACHE))),flush=True)
            reports=time.monotonic()+30
    print(json.dumps(dict(finished=True,iterations=iterations,accepted=accepted,best=best,
                         seconds=time.monotonic()-begun,seed=rngseed)),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--seconds',type=int,default=1200)
    p.add_argument('--seed',type=int,default=2602)
    p.add_argument('--out',type=Path,required=True)
    a=p.parse_args()
    run(a.seconds,a.seed,a.out)
