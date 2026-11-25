import json,math,random,time
from pathlib import Path
random.seed(3451)

def run(N, seconds):
    n=2*N
    xs=[sum(1<<a for a in range(1<<n) if a>>i&1) for i in range(n)]
    edges=[(p,N+l) for p in range(N) for l in [p,(p+1)%N]]
    target=0
    for u,v in edges: target |= xs[u]&xs[v]
    clean=[]
    out=[]
    for p in range(N):
        clean.append((1,N+p,N+(p+1)%N)); w=n+len(clean)-1
        clean.append((0,p,w)); out.append(n+len(clean)-1)
    w=out[0]
    for v in out[1:]: clean.append((1,w,v)); w=n+len(clean)-1
    k=len(clean)-1
    starts=[]
    for j,g in enumerate(clean):
        for replacement in g[1:]:
            gs=[]
            for i,h in enumerate(clean):
                if i==j: continue
                def shift(x):
                    if x==n+j:x=replacement
                    if x>n+j:x-=1
                    return x
                gs.append((h[0],shift(h[1]),shift(h[2])))
            starts.append(gs)
    def evaluate(gs):
        ws=xs[:]
        for op,a,b in gs: ws.append((ws[a]|ws[b]) if op else (ws[a]&ws[b]))
        return (ws[-1]^target).bit_count()
    deadline=time.monotonic()+seconds
    best=1<<n;tries=0;restarts=0
    while time.monotonic()<deadline:
        gs=list(random.choice(starts));score=evaluate(gs)
        for step in range(6000):
            if step%256==0 and time.monotonic()>=deadline:break
            j=random.randrange(k);old=gs[j]
            change=random.randrange(5)
            if change==0: new=(1-old[0],old[1],old[2])
            elif change<=2:new=(old[0],random.randrange(n+j),old[2])
            else:new=(old[0],old[1],random.randrange(n+j))
            gs[j]=new;newscore=evaluate(gs);tries+=1
            T=4.5*(0.01**(step/6000))
            if newscore<=score or random.random()<math.exp((score-newscore)/T):score=newscore
            else:gs[j]=old
            if score<best:
                best=score
                record={'N':N,'gates':k,'best_errors':best,'tries':tries,'circuit':gs}
                print(json.dumps(record),flush=True)
                Path('/tmp/oec/pequalnp-pilot-51/cycle-best-'+str(N)+'.json').write_text(json.dumps(record))
            if best==0:return
        restarts+=1
    print(json.dumps({'N':N,'gates':k,'best_errors':best,'tries':tries,'restarts':restarts,'result':'no exact candidate found; heuristic only'}),flush=True)
run(4,120)
run(5,120)
