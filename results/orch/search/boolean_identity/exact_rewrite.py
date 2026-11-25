import argparse, collections, itertools, json, math, random, sys, time
from pathlib import Path
D=Path(__file__).resolve().parent
search_paths=[D,D.parent,Path.cwd()/'results/orch/search',Path('/workspace/pequalnp-proofs/results/orch/search')]
ARCHIVE=next(path for path in search_paths if (path/'counterexample_q3_repair.py').is_file())
sys.path.insert(0,str(ARCHIVE))
import counterexample_q3_repair as plane

N=26
patterns=plane.POSITIVE+plane.NEGATIVE
TARGET=(1<<len(plane.POSITIVE))-1
ALL=(1<<len(patterns))-1
INPUT=[sum(1<<i for i,z in enumerate(patterns) if z>>j&1) for j in range(N)]

def evaluate(net, override=-1, bit=0):
    ws=INPUT.copy()
    for i,(op,a,b) in enumerate(net,N):
        ws.append(bit if i==override else (ws[a]&ws[b] if op else ws[a]|ws[b]))
    return ws

def seed(rng, mode):
    net=[]; cache={}
    def gate(op,a,b):
        a,b=sorted((a,b))
        if a==b: return a
        expr=(op,a,b)
        if expr not in cache:
            cache[expr]=len(net)+N; net.append(expr)
        return cache[expr]
    def join(nodes):
        nodes=list(nodes); rng.shuffle(nodes)
        while len(nodes)>1:
            x=nodes.pop(); j=rng.randrange(len(nodes)); nodes[j]=gate(0,nodes[j],x)
        return nodes[0]
    selected=set(rng.sample(range(13),rng.randrange(1,5))) if mode in (1,3) else set()
    masks={l:set(plane.LINES[l])-selected for l in range(13)}
    subst=list(range(13)); used=set(); targets=set()
    if mode in (2,3,4):
        for _ in range(1 if mode==2 else rng.choice((2,3,4))):
            pairs=[(l,p) for l,vs in masks.items() for p in vs if len(vs)>1 and p not in used and l not in targets]
            if not pairs: break
            l,p=rng.choice(pairs); used.add(p); targets.add(l)
            others=sorted(masks[l]-{p}); chosen=set(rng.sample(others,rng.randint(1,len(others))))
            masks[l]-=chosen
            subst[p]=gate(1,join([p,*chosen]),gate(0,p,13+l))
    stars=[]
    for p in selected:
        stars.append(gate(1,p,join([13+i for i in range(13) if p in plane.LINES[i]])))
    for l,vs in masks.items():
        if vs: stars.append(gate(1,13+l,join(subst[p] for p in vs)))
    out=join(stars)
    assert out==N+len(net)-1 and evaluate(net)[-1]==TARGET
    return net

def closure(net):
    ans=[0]*N
    for i,(_,a,b) in enumerate(net):
        ans.append((1<<i)|ans[a]|ans[b])
    return ans

def rewrite(net, t, rng, maxsize):
    vals=evaluate(net); ancestors=closure(net)
    target=N+t; bit=1<<t; old=vals[target]
    below=evaluate(net,target,0)[-1]; above=evaluate(net,target,ALL)[-1]
    must1=TARGET&~below; must0=~TARGET&above
    if not must1 or not must0: return
    care=must1|must0
    base=0; todo=[len(vals)-1]
    while todo:
        w=todo.pop()
        if w<N or w==target or base>>(w-N)&1: continue
        base |= 1<<(w-N)
        todo.extend(net[w-N][1:])
    basecount=base.bit_count()
    ds=[i for i,v in enumerate(vals) if not ancestors[i]&bit]
    atoms=[]; known={}
    for i in ds:
        atoms.append((vals[i],ancestors[i]&~base,0,i))
        if i>=N: known[tuple(net[i-N])]=i
    for k,a in enumerate(ds):
        A=vals[a]
        for b in ds[:k]:
            B=vals[b]; deps=(ancestors[a]|ancestors[b])&~base
            if basecount+deps.bit_count()+1>maxsize: continue
            for op,C in [(0,A|B),(1,A&B)]:
                if C==A or C==B: continue
                g=(op,b,a)
                if g not in known: atoms.append((C,deps,1,g))
    found={}
    def save(deps,nnew,ex,kind,value):
        size=basecount+deps.bit_count()+nnew
        if size>maxsize or (size==len(net) and ex==tuple(net[t])): return
        # An exact gate-local semantic change is favored over a pure reassociation.
        key=(size,kind,int(value!=old))
        count,prev=found.get(key,(0,None)); count+=1
        found[key]=(count,ex if rng.randrange(count)==0 else prev)
    for C,deps,c,rep in atoms:
        if (C^old)&care==0: save(deps,c,rep,'divisor',C)
    for outer in (0,1):
        required=must0 if outer else must1
        groups={}
        for C,deps,c,rep in atoms:
            if (must1&~C if outer else must0&C): continue
            cov=(~C if outer else C)&required
            if cov==0 or cov==required: continue
            cost=deps.bit_count()+c
            ls=groups.setdefault(cov,[])
            if len(ls)<3 or cost<ls[-1][0] or (cost==ls[-1][0] and rng.random()<0.025):
                ls.append((cost,rng.random(),C,deps,c,rep))
                ls.sort(key=lambda e:e[:2]); del ls[3:]
        gs=list(groups)
        if len(gs)>350: rng.shuffle(gs); gs=gs[:350]
        for k,sa in enumerate(gs):
            need=required&~sa
            for sb in gs[:k]:
                if need&~sb: continue
                aa=groups[sa]; bb=groups[sb]
                for x,y in ((aa[0],bb[0]),(rng.choice(aa),rng.choice(bb))):
                    _,_,A,ad,ac,a=x; _,_,B,bd,bc,b=y
                    if isinstance(a,int) and isinstance(b,int):
                        opwire=known.get((outer,min(a,b),max(a,b)))
                        if opwire is not None: continue
                    C=A&B if outer else A|B
                    save(ad|bd,1+ac+bc,(outer,a,b),'outer',C)
    if not found: return
    return found

def graft(net,t,replacement):
    memo={}; final=[]; table={}
    def visit(w):
        if isinstance(w,int):
            if w<N: return w
            if w in memo: return memo[w]
            expr=replacement if w==N+t else net[w-N]
            v=visit(expr); memo[w]=v; return v
        op,a,b=w; a,b=sorted([visit(a),visit(b)])
        if a==b: return a
        key=op,a,b
        if key not in table:
            table[key]=N+len(final); final.append(key)
        return table[key]
    w=visit(N+len(net)-1)
    assert w==N+len(final)-1
    return final

def main():
    p=argparse.ArgumentParser(); p.add_argument('--seconds',type=int,default=540); p.add_argument('--seed',type=int,default=76131)
    args=p.parse_args(); rng=random.Random(args.seed); start=time.monotonic()
    stats=collections.Counter(); best=100; min_mixed=100; n=0; last=0
    seednum=0
    while time.monotonic()-start<args.seconds:
        mode=seednum%5
        net=seed(rng,mode); seednum+=1; steps=0; nochange=0; oldsize=len(net)
        ceiling=max(oldsize,min(73,67+seednum%6))
        for step in range(80):
            if time.monotonic()-start>=args.seconds: break
            t=rng.randrange(len(net))
            options=rewrite(net,t,rng,ceiling); n+=1
            if options:
                keys=list(options)
                temper=max(.26,1.2*(1-step/80))
                weights=[math.exp((len(net)-k[0])/temper)*(1 if k[1]=='divisor' else 1.5)*(1 if k[2]==0 else 4) for k in keys]
                key=rng.choices(keys,weights)[0]; ex=options[key][1]
                new=graft(net,t,ex)
                if new!=net:
                    assert evaluate(new)[-1]==TARGET
                    stats[(len(net),len(new))]+=1
                    net=new; steps+=1
            if len(net)<best:
                best=len(net); record=dict(gates=best,seed=args.seed,iteration=n,mode=mode,wall=time.monotonic()-start,circuit=net)
                (D/('best-'+str(args.seed)+'.json')).write_text(json.dumps(record))
                print('best',best,'iteration',n,'seedmode',mode,'elapsed',round(time.monotonic()-start,2),flush=True)
            if len(net)<64:
                assert plane.evaluate(net,patterns)==TARGET
                print('WITNESS',json.dumps(net),flush=True); return
            if time.monotonic()-last>30:
                print('progress',n,seednum,steps,len(net),best,round(time.monotonic()-start,2),flush=True)
                last=time.monotonic()
    print('finished',json.dumps(dict(best=best,queries=n,seeds=seednum,transitions={str(k):v for k,v in stats.items()})),flush=True)
if __name__=='__main__': main()
