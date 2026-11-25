import argparse, collections, itertools, json, math, random, time
import exact_rewrite as one
import joint_rewrite as two
from pathlib import Path
D=Path(__file__).resolve().parent
from counterexample_q3_repair import LINES as PL, evaluate as plane_eval, POSITIVE as PP, NEGATIVE as NN
verts=9
center=sorted(set(range(13))-PL[0]); other=list(range(1,13))
P=[tuple(i for i,p in enumerate(center) if p in PL[l]) for l in other]
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
assert len(pos)==36 and len(neg)<=512

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
    split=set(rng.sample(range(verts),rng.choice((4,5,6,7)))) if mode in (3,5) else set()
    for l,S in enumerate(mask):
        if not S:continue
        vs=[subst[p] for p in S]; rng.shuffle(vs)
        if l in split and len(vs)>1:
            i=rng.randrange(1,len(vs))
            stars.extend([G(1,len(P)+l,R(vs[:i])),G(1,len(P)+l,R(vs[i:]))])
        else: stars.append(G(1,len(P)+l,R(vs)))
    out=R(stars)
    assert out==NV+len(net)-1 and one.evaluate(net)[-1]==target
    return net

def baseline_sigs(opposite,neighborhoods):
    universe=sum(1<<i for i in opposite)
    patterns=[1<<v for v in opposite]+[universe^sum(1<<v for v in S) for S in neighborhoods]
    mask=[sum(1<<j for j,pat in enumerate(patterns) if pat>>i&1) for i in range(NV)]
    targets={sum(1<<j for j,pat in enumerate(patterns) if any(pat>>i&1 for i in S)):k for k,S in enumerate(neighborhoods)}
    return mask,targets

point_base=baseline_sigs(range(len(P)),lines)
line_base=baseline_sigs(range(len(P),NV),[{len(P)+i for i in S} for S in P])

def present_mask(net,base):
    inp,targets=base; ws=inp.copy()
    for op,a,b in net: ws.append(ws[a]&ws[b] if op else ws[a]|ws[b])
    return {targets[v] for v in ws if v in targets}

def number_present(net,base):
    return len(present_mask(net,base))

def pressure(net):
    ps=present_mask(net,point_base); ls=present_mask(net,line_base)
    tp=len(ps); tl=len(ls)
    dp=sum(S<=ls for S in lines); dl=sum(all(i in ps for i in S) for S in P)
    return max(0,tp-5,9+3*tp-dl-23)+max(0,tl-6,12+2*tl-dp-23)

def bad_read1(c):
    a=[s&target if i<len(P) else 0 for i,s in enumerate(inputs)]; b=[s&target if i>=len(P) else 0 for i,s in enumerate(inputs)]; h=[0]*NV
    for op,i,j in c:
        A,B,H=(0,0,(a[i]&b[j])|(a[j]&b[i])) if op else (a[i]|a[j],b[i]|b[j],h[i]|h[j])
        a.append(A); b.append(B);h.append(H)
    return [e for i,e in enumerate(edges) if not (h[-1]>>i&1)]

def full_plane(c):
    rec={i:13+l for i,l in enumerate(other)}
    rec.update({len(P)+i:p for i,p in enumerate(center)}); out=[]
    for g,(op,i,j) in enumerate(c,NV):
        rec[g]=26+len(out); out.append((op,rec[i],rec[j]))
    x=26+len(out)-1
    for p in sorted(PL[0]):
        flags=[13+l for l,V in enumerate(PL) if p in V]; w=flags[0]
        for v in flags[1:]: out.append((0,w,v)); w=26+len(out)-1
        out.append((1,p,w)); s=26+len(out)-1
        out.append((0,x,s)); x=26+len(out)-1
    assert len(out)==len(c)+20
    assert plane_eval(out,PP+NN)==(1<<52)-1
    return {'infinity_line':0,'affine_points':center,'gates':len(out),'circuit':out}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--seconds',type=int,default=420); ap.add_argument('--seed',type=int,default=76135); args=ap.parse_args()
    rng=random.Random(args.seed); start=last=time.monotonic(); tries=seeds=0; totals=collections.Counter(); best=44; non=99; eligible=999
    bank=[]
    while time.monotonic()-start<args.seconds:
        mode=seeds%7; net=rng.choice(bank) if mode==6 and bank else seed(rng,mode); seeds+=1
        for step in range(48):
            if time.monotonic()-start>=args.seconds: break
            cap=max(len(net),45+seeds%4)
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
            # Blend ordinary size exploration with the necessary present-row constraints.
            baseweights=[weight(k) for k in keys]
            chosen=list(dict.fromkeys(rng.choices(keys,baseweights,k=5)))
            choices=[]; relative=[]
            for k in chosen:
                repl=opts[k][1]
                candidate=two.pair_graft(net,NV+t,NV+u,*repl) if tryjoint else one.graft(net,t,repl)
                choices.append(candidate)
                relative.append(math.exp(-.95*pressure(candidate)/temp) if seeds%3 else 1)
            new=rng.choices(choices,relative)[0]
            assert one.evaluate(new)[-1]==target
            totals[(len(net),len(new))]+=1; net=new
            bad=bad_read1(net)
            if not pressure(net) and len(net)<eligible:
                eligible=len(net)
                note=dict(iteration=tries,gates=eligible,circuit=net,positive=36,negative=len(neg),nonread=bad,point_present=number_present(net,point_base),line_present=number_present(net,line_base),full_plane_gates=full_plane(net)['gates'])
                (D/'affine-best-eligible.json').write_text(json.dumps(note))
                print('present-threshold control',eligible,note['point_present'],note['line_present'],tries,flush=True)
            if len(net)<best or (bad and len(net)<non):
                note=dict(iteration=tries,elapsed=time.monotonic()-start,seeds=seeds,gates=len(net),circuit=net,positive=36,negative=len(neg),nonread=bad,point_present=number_present(net,point_base),line_present=number_present(net,line_base))
                (D/('affine-best-'+str(len(net))+'.json')).write_text(json.dumps(note))
                print('best',len(net),bad,tries,flush=True)
                best=min(best,len(net))
                if bad: non=min(non,len(net))
                if len(net)<44:
                    (D/'affine-q4-witness.json').write_text(json.dumps(full_plane(net)))
                    return
            if (bad or not pressure(net)) and len(net)<=46 and rng.random()<.035:
                if len(bank)<80: bank.append(net)
                else: bank[rng.randrange(len(bank))]=net
            if time.monotonic()-last>30:
                print('progress',tries,seeds,len(net),best,non,len(bank),round(time.monotonic()-start,1),flush=True); last=time.monotonic()
    print('finished',tries,seeds,best,non,dict(totals),flush=True)
if __name__=='__main__':main()
