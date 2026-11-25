import argparse, collections, itertools, json, math, random, time
from exact_rewrite import D,N,INPUT,ALL,TARGET,plane,patterns,closure,evaluate,seed
from seed65 import c as seed65,bad_edges


def graph_values(net,t,z,u,v):
    ws=INPUT.copy()
    for i,(op,a,b) in enumerate(net,N):
        ws.append(z if i==t else v if i==u else (ws[a]&ws[b] if op else ws[a]|ws[b]))
    return ws[-1]

def pair_graft(net,t,u,a,b):
    memo={}; gates=[]; defs={}
    def visit(x):
        if isinstance(x,int):
            if x<N: return x
            if x in memo: return memo[x]
            w=visit(a if x==t else b if x==u else net[x-N])
            memo[x]=w; return w
        op,left,right=x; l,r=sorted((visit(left),visit(right)))
        if l==r: return l
        key=op,l,r
        if key not in defs:
            defs[key]=N+len(gates); gates.append(key)
        return defs[key]
    w=visit(N+len(net)-1); assert w==N+len(gates)-1
    return gates

def divs(net,t,u,rng,cap):
    ws=evaluate(net); ac=closure(net); killed=(1<<(t-N))|(1<<(u-N))
    base=0; todo=[len(ws)-1]
    while todo:
        i=todo.pop()
        if i<N or i in (t,u) or base>>(i-N)&1: continue
        base|=1<<(i-N); todo.extend(net[i-N][1:])
    ds=[i for i in range(len(ws)) if not ac[i]&killed]
    used={(int(op),min(i,j),max(i,j)):k for k,(op,i,j) in enumerate(net,N) if k in ds}
    atoms=[(ws[i],ac[i]&~base,0,i) for i in ds]; room=cap-base.bit_count()
    for k,i in enumerate(ds):
        I=ws[i]
        for j in ds[:k]:
            J=ws[j]; deps=(ac[i]|ac[j])&~base
            if deps.bit_count()+1>room: continue
            for op,F in [(0,I|J),(1,I&J)]:
                g=(op,j,i)
                if F not in (I,J) and g not in used: atoms.append((F,deps,1,g))
    return atoms,room

def candidates(atoms,m1,m0,pc,nc,room,rng,depth):
    # For each interaction signature, retain a handful of functions of lowest standalone cost.
    sel={}
    def save(v,d,c,r):
        if m1&~v or m0&v: return
        key=v&(pc|nc); cost=d.bit_count()+c
        if cost>room:return
        group=sel.setdefault(key,[])
        if len(group)<3 or cost<group[-1][0] or (cost==group[-1][0] and rng.random()<.04):
            group.append((cost,rng.random(),v,d,c,r)); group.sort(key=lambda x:x[:2]); del group[3:]
    for v,d,c,r in atoms: save(v,d,c,r)
    if depth:
        # Compose a new gate with a single existing wire, for at most two gates per output.
        leaves=[a for a in atoms if a[2]==0]
        for outer in (0,1):
            pool=[a for a in atoms if not (m1&~a[0] if outer else m0&a[0])]
            left=[a for a in leaves if not (m1&~a[0] if outer else m0&a[0])]
            if len(pool)*len(left)>65000:
                pool=rng.sample(pool,max(1,65000//max(1,len(left))))
            for va,da,ca,ra in pool:
                if not ca: continue
                for vb,db,cb,rb in left:
                    v=va&vb if outer else va|vb
                    if v==va or v==vb: continue
                    save(v,da|db,ca+1,(outer,ra,rb))
    return sel

def query(net,t,u,rng,cap,depth):
    A00=graph_values(net,t,0,u,0); A01=graph_values(net,t,0,u,ALL); A10=graph_values(net,t,ALL,u,0); A11=graph_values(net,t,ALL,u,ALL)
    neg=ALL^TARGET
    a1=TARGET&~A01; a0=neg&A10; b1=TARGET&~A10; b0=neg&A01
    pc=TARGET&~A00&A10&A01; nc=neg&A11&~A10&~A01
    if not (pc|nc): return {}
    atoms,room=divs(net,t,u,rng,cap)
    sa=candidates(atoms,a1,a0,pc,nc,room,rng,depth)
    sb=candidates(atoms,b1,b0,pc,nc,room,rng,depth)
    if not sa or not sb: return {}
    ax=list(sa); bx=list(sb)
    if len(ax)*len(bx)>80000:
        if len(ax)>len(bx): ax=rng.sample(ax,max(1,80000//len(bx)))
        else: bx=rng.sample(bx,max(1,80000//len(ax)))
    res={}
    for av in ax:
        need=pc&~av; forbid=nc&av
        for bv in bx:
            if need&~bv or forbid&bv: continue
            for r1 in sa[av]:
                for r2 in sb[bv]:
                    _,_,v1,d1,c1,g1=r1; _,_,v2,d2,c2,g2=r2
                    sh=0
                    if isinstance(g1,tuple) and isinstance(g2,tuple):
                        def inn(g): return {g}|{a for a in g[1:] if isinstance(a,tuple)}
                        sh=len(inn(g1)&inn(g2))
                    total=(d1|d2).bit_count()+c1+c2-sh
                    if total>room: continue
                    size=cap-room+total
                    key=(size,(g1!=tuple(net[t-N]))+(g2!=tuple(net[u-N])))
                    count,best=res.get(key,(0,None)); count+=1
                    res[key]=(count,(g1,g2) if rng.randrange(count)==0 else best)
    return res

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--seconds',type=int,default=420); ap.add_argument('--seed',type=int,default=76132)
    args=ap.parse_args(); rng=random.Random(args.seed); start=time.monotonic(); last=start
    tries=seeds=0; best=64; nonreadbest=65; mingates={}; transitions=collections.Counter()
    bank=[seed65]
    while time.monotonic()-start<args.seconds:
        mode=seeds%7
        net=bank[rng.randrange(len(bank))] if mode>=5 else seed(rng,mode)
        seeds+=1
        for step in range(35):
            if time.monotonic()-start>=args.seconds: break
            t,u=sorted(rng.sample(range(N,N+len(net)),2))
            if rng.random()<.45:
                # Choose two output branches, or wires with overlapping functional dependencies.
                parents=[i for i,g in enumerate(net,N) if g[0] and i!=t]
                if parents and rng.random()<.5: u=rng.choice(parents)
                else:
                    ds=[v for v in net[t-N][1:] if v>=N]
                    if ds: u=rng.choice(ds)
            if t==u: continue
            cap=min(74,max(len(net),68))
            options=query(net,t,u,rng,cap,1); tries+=1
            if options:
                keys=list(options); temp=max(.31,1.1-step/40)
                key=rng.choices(keys,[math.exp((len(net)-k[0])/temp)*(.15 if k[1]==0 else 1 if k[1]==1 else 4) for k in keys])[0]
                net2=pair_graft(net,t,u,*options[key][1])
                assert evaluate(net2)[-1]==TARGET
                old=len(net); net=net2; transitions[(old,len(net))]+=1
                nonread=bad_edges(net)
                if len(net)<best or (nonread and len(net)<nonreadbest):
                    note={'circuit':net,'gates':len(net),'non_read1':nonread,'all_errors':(plane.evaluate(net,patterns)^TARGET).bit_count(),'iteration':tries,'seed':args.seed,'elapsed':time.monotonic()-start}
                    (D/('joint-best-'+str(args.seed)+'.json')).write_text(json.dumps(note))
                    print('best',len(net),nonread,tries,flush=True)
                    best=min(best,len(net))
                    if nonread: nonreadbest=min(len(net),nonreadbest)
                    if len(net)<=63:return
                if nonread and len(net)<=66 and rng.random()<.1:
                    if len(bank)<96: bank.append(net)
                    else: bank[rng.randrange(1,len(bank))]=net
            if time.monotonic()-last>30:
                print('progress',tries,seeds,len(net),len(bank),round(time.monotonic()-start,1),flush=True); last=time.monotonic()
    print('finished',tries,seeds,best,nonreadbest,dict(transitions),flush=True)
if __name__=='__main__': main()
