import argparse,json,random,time
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument("--seconds",type=float,default=240);ap.add_argument("--seed",type=int,default=144);args=ap.parse_args()
r=random.Random(args.seed)
E=[(p,7+l) for l in range(7) for p in (l,(l+1)%7,(l+3)%7)]
def target(s):return any(s>>p&1 and s>>l&1 for p,l in E)
positive=[(1<<p)|(1<<l) for p,l in E]
negative=[s for s in range(1<<14) if not target(s) and all(target(s|1<<i) for i in range(14) if not(s>>i&1))]
samples=positive+negative
inputs=[sum(((s>>i)&1)<<j for j,s in enumerate(samples)) for i in range(14)]
goal=(1<<len(positive))-1
mask=(1<<len(samples))-1
base=[]
for l in range(7):
    p=[l,(l+1)%7,(l+3)%7]
    base.append([1,p[0],p[1]]);a=14+len(base)-1
    base.append([1,a,p[2]]);a=14+len(base)-1
    base.append([0,a,7+l])
outs=[16+3*l for l in range(7)]
z=outs[0]
for a in outs[1:]:base.append([1,z,a]);z=14+len(base)-1
assert len(base)==27

def ev(gates):
    v=inputs.copy()
    for op,a,b in gates:v.append(v[a]|v[b] if op else v[a]&v[b])
    bad=v[-1]^goal
    return bad.bit_count(),v[-1],v
assert ev(base)[0]==0
print(json.dumps({"edges":E,"positive_count":len(positive),"negative_count":len(negative),"negative":negative,"baseline":base,"baseline_size":len(base)}),flush=True)
out=Path(__file__).parent
(out/"fano_cases.json").write_text(json.dumps({"edges":E,"positive":positive,"negative":negative,"baseline":base},indent=2))

def smaller():
    d=r.randrange(len(base));repl=base[d][r.randrange(1,3)];gone=14+d
    def remap(i):
        if i==gone:return repl
        return i-1 if i>gone else i
    return [[o,remap(a),remap(b)] for j,(o,a,b) in enumerate(base) if j!=d]

start=time.monotonic();it=0;best=999;last=0;restarts=0
while time.monotonic()-start<args.seconds:
    g=smaller();score,_,_=ev(g);stale=0;restarts+=1
    for _ in range(30000):
        it+=1;stale+=1
        if time.monotonic()-start>=args.seconds:break
        changed=[]
        for k in range(1 if r.random()<0.94 else r.randrange(2,5)):
            i=r.randrange(len(g));j=r.randrange(3);old=g[i][j]
            g[i][j]=r.randrange(2) if j==0 else r.randrange(14+i)
            changed.append((i,j,old))
        new,y,v=ev(g)
        if new<=score or (stale>1000 and r.random()<0.0001):
            if new<score:stale=0
            score=new
        else:
            for i,j,old in reversed(changed):g[i][j]=old
        if score<best:
            best=score
            rec={"seed":args.seed,"elapsed":time.monotonic()-start,"iterations":it,"errors":best,"gates":g}
            print(json.dumps(rec),flush=True);(out/"best.json").write_text(json.dumps(rec,indent=2))
        if score==0:
            ok=True
            for s in range(1<<14):
                v=[bool(s>>i&1) for i in range(14)]
                for o,a,b in g:v.append(v[a] or v[b] if o else v[a] and v[b])
                if v[-1]!=target(s):ok=False;break
            print("FOUND_FULL_VERIFIED",ok,flush=True)
            (out/"witness.json").write_text(json.dumps({"verified":ok,"gates":g},indent=2));raise SystemExit(0)
        if time.monotonic()-last>=20:
            last=time.monotonic();print(json.dumps({"elapsed":last-start,"iterations":it,"restarts":restarts,"best":best}),flush=True)
print(json.dumps({"finished":True,"elapsed":time.monotonic()-start,"iterations":it,"restarts":restarts,"best":best}),flush=True)
