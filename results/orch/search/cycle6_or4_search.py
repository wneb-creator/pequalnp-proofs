import argparse
import json
import math
import random
import time
from pathlib import Path

N=6
ALL=(1<<(1<<N))-1
EDGES=[(i,(i+1)%N) for i in range(N)]
TARGET=sum(int(any((x>>a)&(x>>b)&1 for a,b in EDGES))<<x for x in range(1<<N))
INPUTS=[sum(((x>>i)&1)<<x for x in range(1<<N)) for i in range(N)]


def prod(mask,wires):
    val=ALL
    while mask:
        bit=mask&-mask
        val&=wires[bit.bit_length()-1]
        mask-=bit
    return val


def evaluate(gs):
    w=INPUTS.copy()
    for a,b in gs[:4]:w.append(prod(a,w)|prod(b,w))
    v=prod(gs[4],w)
    return (v^TARGET).bit_count()


def seed(rng):
    gs=[(1<<1,1<<5),(1<<1,1<<3),(1<<3,1<<5),((1<<0)|(1<<6),(1<<2)|(1<<7)),(1<<9,(1<<4)|(1<<8))]
    output=1<<10
    j=rng.randrange(5);dead=N+j;repl=gs[j][rng.randrange(2)]
    def ren(mask):
        if mask&(1<<dead):mask=(mask^(1<<dead))|repl
        return (mask&((1<<dead)-1))|((mask>>(dead+1))<<dead)
    g=[(ren(a),ren(b)) if i>j else (a,b) for i,(a,b) in enumerate(gs) if i!=j]
    return tuple(g)+(ren(output),)


def mutate(gs,rng):
    g=list(gs)
    for _ in range(rng.choices([1,2,3,6],[75,18,6,1])[0]):
        j=rng.randrange(5)
        if j==4:
            mask=g[j];bits=N+4
            mask^=1<<rng.randrange(bits)
            if not mask:mask=1<<rng.randrange(bits)
            g[j]=mask
        else:
            a,b=g[j];side=rng.randrange(2);mask=(a,b)[side];bits=N+j
            if rng.randrange(8)==0:
                mask=0
                for _ in range(rng.randint(1,4)):mask|=1<<rng.randrange(bits)
            else:mask^=1<<rng.randrange(bits)
            if not mask:mask=1<<rng.randrange(bits)
            g[j]=(mask,b) if side==0 else (a,mask)
    return tuple(g)


def run(seconds,rngseed,out):
    rng=random.Random(rngseed);began=time.monotonic();iters=0;accepted=0
    chains=[]
    for k in range(24):
        g=seed(rng);chains.append([g,evaluate(g),[0,.1,.25,.5,1,2][k%6],0])
    best=100000;next_report=began+30
    while time.monotonic()-began<seconds:
        iters+=1;chain=rng.choice(chains);g=mutate(chain[0],rng);e=evaluate(g)
        if e<best:
            best=e
            data=dict(seed=rngseed,iterations=iters,seconds=time.monotonic()-began,errors=e,
                      normalized_or_gates=g,description='Each OR operand is an arbitrary nonempty conjunction of earlier atoms; final mask is a conjunction')
            out.write_text(json.dumps(data)+'\n')
            print(json.dumps(data),flush=True)
        if e==0:
            print(json.dumps(dict(found=True,iterations=iters)),flush=True);return
        delta=e-chain[1]
        if delta<=0 or (chain[2]>0 and rng.random()<math.exp(-delta/chain[2])):
            chain[0],chain[1]=g,e;accepted+=1
        chain[3]+=1
        if chain[3]>=50000:
            g=seed(rng);chain[0],chain[1],chain[3]=g,evaluate(g),0
        if time.monotonic()>next_report:
            print(json.dumps(dict(progress=True,iterations=iters,accepted=accepted,best=best,seconds=time.monotonic()-began)),flush=True)
            next_report=time.monotonic()+30
    print(json.dumps(dict(finished=True,iterations=iters,accepted=accepted,best=best,seconds=time.monotonic()-began)),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--seconds',type=int,default=1200);p.add_argument('--seed',type=int,default=2602);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();run(a.seconds,a.seed,a.out)
