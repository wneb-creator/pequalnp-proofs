import argparse, json, random, time
from pathlib import Path
p=argparse.ArgumentParser(); p.add_argument('--seconds',type=float,default=120); p.add_argument('--seed',type=int,default=670); a=p.parse_args()
rng=random.Random(a.seed)
mask=(1<<512)-1
raw=[sum(((m>>i)&1)<<m for m in range(512)) for i in range(9)]
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
target=sum(int(any(m>>u&1 and m>>v&1 for u,v in edges))<<m for m in range(512))
coverlist=[[1,2,4,5,8],[0,1,3,7,8],[0,2,3,5,6]]
def build16():
    cover=rng.choice(coverlist)[:]; rng.shuffle(cover)
    owned={v:[] for v in cover}
    for u,v in edges:
        opts=[x for x in [u,v] if x in owned]; c=rng.choice(opts); owned[c].append(v if c==u else u)
    gates=[]; outs=[]
    for c,ns in owned.items():
        rng.shuffle(ns); out=ns[0]
        for v in ns[1:]: gates.append((1,out,v)); out=8+len(gates)
        gates.append((0,c,out)); outs.append(8+len(gates))
    rng.shuffle(outs); out=outs[0]
    for v in outs[1:]: gates.append((1,out,v)); out=8+len(gates)
    assert len(gates)==16
    return gates

def remove(gs,j,side):
    wire=9+j; src=gs[j][side]
    result=[]
    for i,(op,u,v) in enumerate(gs):
        if i==j: continue
        def f(x):
            if x==wire: x=src
            return x-1 if x>wire else x
        result.append((op,f(u),f(v)))
    return result

def score(gs):
    w=raw[:]
    for j,(op,u,v) in enumerate(gs):
        av=w[u] if u<len(w) else 0
        bv=w[v] if v<len(w) else 0
        w.append(av&bv if op==0 else av|bv if op==1 else mask^av)
    return (w[-1]^target).bit_count()

def mutate(gs,n=1):
    out=gs[:]
    for _ in range(n):
        j=rng.randrange(15); op,u,v=out[j]
        mode=rng.randrange(4)
        if mode==0: op=rng.randrange(3)
        elif mode==1: u=rng.randrange(10+j)
        elif mode==2: v=rng.randrange(10+j)
        else: op=rng.randrange(3); u=rng.randrange(10+j); v=rng.randrange(10+j)
        out[j]=(op,u,v)
    return out

original_target=target
target=sum(((~original_target>>(511-m))&1)<<m for m in range(512))
def dual_seed():
    gs=build16(); reps=[1<<i for i in range(9)]; pairs=[]
    for op,u,v in gs:
        if op==0: reps.append(reps[u]|reps[v])
        else:
            pairs.append((reps[u],reps[v])); reps.append(1<<(8+len(pairs)))
    out=reps[-1]
    assert len(pairs)==11
    assert evalcost(pairs,out)==0
    j=rng.randrange(11); pos=9+j; bit=1<<pos
    left,right=pairs[j]
    subst=rng.choice([left,right,left|right])
    def remap(m):
        if m&bit: m=(m^bit)|subst
        return (m&(bit-1))|((m>>(pos+1))<<pos)
    pairs=[(remap(u),remap(v)) for k,(u,v) in enumerate(pairs) if k!=j]
    return pairs,remap(out)
def subset_or(w,bits):
    out=0
    while bits:
        bit=bits&-bits; out|=w[bit.bit_length()-1]; bits^=bit
    return out

def evalcost(pairs,out):
    w=raw[:]
    for left,right in pairs:
        w.append(subset_or(w,left)&subset_or(w,right))
    result=subset_or(w,out)
    return (result^target).bit_count()

def mutatecost(pairs,out):
    alt=pairs[:]
    if rng.random()<.09:
        bit=1<<rng.randrange(9,19); out^=bit
    else:
        j=rng.randrange(10); side=rng.randrange(2); m=alt[j][side]
        mode=rng.randrange(20)
        if mode==0: m=1<<rng.randrange(9+j)
        elif mode==1: m=rng.randrange(1<<(9+j))
        else: m^=1<<rng.randrange(9+j)
        alt[j]=(m,alt[j][1]) if side==0 else (alt[j][0],m)
    return alt,out
start=time.monotonic(); best=513; tries=0; restarts=0
while time.monotonic()-start<a.seconds:
    pairs,out=dual_seed(); current=evalcost(pairs,out); restarts+=1; stale=0
    for it in range(12000):
        tries+=1
        alt,o=mutatecost(pairs,out); sc=evalcost(alt,o)
        if sc<best:
            best=sc; record={'elapsed':time.monotonic()-start,'wrong':best,'dual_and_gates':alt,'dual_output_mask':o,'tries':tries,'restarts':restarts}; print(json.dumps(record),flush=True)
            Path('/tmp/oec/pequalnp-pilot-32/finite_cases/search_or10-best.json').write_text(json.dumps(record,indent=2)+'\n')
        if sc==0:
            print('EXACT COUNT COUNTEREXAMPLE',flush=True); raise SystemExit(0)
        if sc<=current or (stale>800 and rng.random()<.002):
            improved=sc<current; pairs,out,current=alt,o,sc; stale=0 if improved else stale+1
        else: stale+=1
        if tries%1000==0 and time.monotonic()-start>=a.seconds: break
print(json.dumps({'result':'no exact OR10 circuit found','best_wrong':best,'tries':tries,'restarts':restarts,'elapsed':time.monotonic()-start}),flush=True)
