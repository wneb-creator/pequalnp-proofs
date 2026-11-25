import argparse, collections, itertools, json, math, random, time
import exact_rewrite as one
import joint_rewrite as two
from pathlib import Path
D=Path(__file__).resolve().parent
verts=8
P=[(i,4+j) for i in range(4) for j in range(4)]+[tuple(range(4)),tuple(range(4,8))]
NV=len(P)+verts
lines=[{j for j,p in enumerate(P) if l in p} for l in range(verts)]
edges=[(p,len(P)+l) for l in range(verts) for p in sorted(lines[l])]
pos=[(1<<p)|(1<<l) for p,l in edges]
neg=[]
for s in range(1<<verts):
    alive=[i for i,ps in enumerate(P) if all(s>>p&1 for p in ps)]
    if sum(1<<p for p in {p for i in alive for p in P[i]})!=s: continue
    xs=sum(1<<i for i in alive)
    neg.append(xs|(((1<<verts)-1-s)<<len(P)))
pat=pos+neg; target=(1<<len(pos))-1; allrows=(1<<len(pat))-1
inputs=[sum(1<<i for i,a in enumerate(pat) if a>>v&1) for v in range(NV)]
for m in (one,two):
    m.N=NV; m.INPUT=inputs; m.TARGET=target; m.ALL=allrows; m.patterns=pat
assert len(pos)==40 and len(neg)<=256

def seed(rng,mode):
    net=[]; cache={}
    def G(o,a,b):
        a,b=sorted((a,b)); k=o,a,b
        if a==b: return a
        if k not in cache: cache[k]=NV+len(net); net.append(k)
        return cache[k]
    def R(ns):
        ns=list(ns); rng.shuffle(ns)
        while len(ns)>1:
            a=ns.pop(); j=rng.randrange(len(ns)); ns[j]=G(0,ns[j],a)
        return ns[0]
    # Randomly transfer individual entire point stars or individual incidence pairs.
    covered={}
    if mode in (2,4,5):
        for p in rng.sample(range(len(P)),rng.choice((1,1,2,2,3))):
            covered[p]=set(P[p]) if mode!=5 else {rng.choice(P[p])}
    mask=[{p for p in ps if l not in covered.get(p,())} for l,ps in enumerate(lines)]
    subst=list(range(len(P)))
    if mode in (1,3,4):
        used=set(); flags=set()
        for _ in range(1 if mode==1 else rng.choice((1,2,3))):
            pairs=[(l,p) for l,S in enumerate(mask) if len(S)>1 and l not in flags for p in S if p not in used]
            if not pairs: break
            l,p=rng.choice(pairs); used.add(p);flags.add(l)
            others=sorted(mask[l]-{p})
            A=set(rng.sample(others,rng.randint(1,len(others)))); mask[l]-=A
            if rng.random()<.5: subst[p]=G(1,R([p,*A]),G(0,p,len(P)+l))
            else: subst[p]=G(0,p,G(1,R(A),len(P)+l))
    stars=[G(1,p,R(len(P)+l for l in ls)) for p,ls in covered.items()]
    stars += [G(1,len(P)+l,R(subst[p] for p in S)) for l,S in enumerate(mask) if S]
    out=R(stars)
    assert out==NV+len(net)-1 and one.evaluate(net)[-1]==target
    return net

def bad_read1(c):
    a=[s&target if i<len(P) else 0 for i,s in enumerate(inputs)]; b=[s&target if i>=len(P) else 0 for i,s in enumerate(inputs)]; h=[0]*NV
    for op,i,j in c:
        A,B,H=(0,0,(a[i]&b[j])|(a[j]&b[i])) if op else (a[i]|a[j],b[i]|b[j],h[i]|h[j])
        a.append(A); b.append(B);h.append(H)
    return [e for i,e in enumerate(edges) if not (h[-1]>>i&1)]

def full_plane(c):
    delta=[0,1,4,14,16]
    full=[{(l+i)%21 for i in delta} for l in range(21)]
    assert all(len(A&B)==1 for A,B in itertools.combinations(full,2))
    a,b=0,1
    hv=[l for l in range(21) if a in full[l] and b not in full[l]]+[l for l in range(21) if b in full[l] and a not in full[l]]
    assert len(hv)==8
    rec={i:next(iter(full[hv[i//4]]&full[hv[4+i%4]])) for i in range(16)}
    rec[16]=a; rec[17]=b
    assert all({rec[i] for i in lines[l]}==full[hv[l]] for l in range(verts))
    rec.update({len(P)+a:21+l for a,l in enumerate(hv)}); out=[]
    for g,(op,i,j) in enumerate(c,NV):
        rec[g]=42+len(out); out.append((op,rec[i],rec[j]))
    x=42+len(out)-1
    for l,W in enumerate(full):
        if l in hv: continue
        S=sorted(W); a=S[0]
        for b in S[1:]: out.append((0,a,b)); a=42+len(out)-1
        out.append((1,a,21+l)); s=42+len(out)-1
        out.append((0,x,s)); x=42+len(out)-1
    assert len(out)==len(c)+78
    return {'difference_set':delta,'eight_lines':hv,'gates':len(out),'circuit':out}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--seconds',type=int,default=420); ap.add_argument('--seed',type=int,default=76134); args=ap.parse_args()
    rng=random.Random(args.seed); start=last=time.monotonic(); tries=seeds=0; totals=collections.Counter(); best=47; non=99
    bank=[]
    while time.monotonic()-start<args.seconds:
        mode=seeds%7; net=rng.choice(bank) if mode==6 and bank else seed(rng,mode); seeds+=1
        for step in range(48):
            if time.monotonic()-start>=args.seconds: break
            cap=max(len(net),48+seeds%4)
            t=rng.randrange(len(net))
            tryjoint=rng.random()<.52
            if tryjoint:
                u=rng.choice([i for i in range(len(net)) if i!=t]); opts=two.query(net,NV+t,NV+u,rng,cap,1)
            else:
                opts=one.rewrite(net,t,rng,cap)
            tries+=1
            if not opts: continue
            keys=list(opts); temp=.31+(1-step/48)*.55
            def weight(k):
                if tryjoint: structural=.04 if k[1]==0 else 1 if k[1]==1 else 4
                else: structural=1 if k[1]=='divisor' else (4 if k[2] else 2)
                return math.exp((len(net)-k[0])/temp)*structural
            k=rng.choices(keys,[weight(k) for k in keys])[0]; repl=opts[k][1]
            if tryjoint: new=two.pair_graft(net,NV+t,NV+u,*repl)
            else:new=one.graft(net,t,repl)
            assert one.evaluate(new)[-1]==target
            totals[(len(net),len(new))]+=1; net=new
            bad=bad_read1(net)
            if len(net)<best or (bad and len(net)<non):
                note=dict(iteration=tries,elapsed=time.monotonic()-start,seeds=seeds,gates=len(net),circuit=net,positive=40,negative=len(neg),nonread=bad)
                (D/('two-pencil-best-'+str(len(net))+'.json')).write_text(json.dumps(note))
                print('best',len(net),bad,tries,flush=True)
                best=min(best,len(net))
                if bad: non=min(non,len(net))
                if len(net)<47:
                    (D/'two-pencil-q4-witness.json').write_text(json.dumps(full_plane(net)))
                    return
            if bad and len(net)<=49 and rng.random()<.035:
                if len(bank)<80: bank.append(net)
                else: bank[rng.randrange(len(bank))]=net
            if time.monotonic()-last>30:
                print('progress',tries,seeds,len(net),best,non,len(bank),round(time.monotonic()-start,1),flush=True); last=time.monotonic()
    print('finished',tries,seeds,best,non,dict(totals),flush=True)
if __name__=='__main__':main()
