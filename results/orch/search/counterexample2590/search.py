import argparse,json,random,time,math
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument("--seconds",type=float,default=600);ap.add_argument("--seed",type=int,default=2590);args=ap.parse_args();r=random.Random(args.seed)
out=Path(__file__).parent;cases=json.loads((out/"petersen_cases.json").read_text());E=cases["edges"];samples=cases["positive"]+cases["negative"]
inputs=[sum(((s>>i)&1)<<j for j,s in enumerate(samples)) for i in range(10)]
goal=(1<<15)-1;mask=(1<<30)-1

def target(s):return any(s>>p&1 and s>>l&1 for p,l in E)
def ev(gates):
 v=inputs.copy()
 for op,a,b in gates:v.append(v[a]|v[b] if op else v[a]&v[b])
 bad=v[-1]^goal
 return bad.bit_count(),v[-1],v

def baseline():
 indep=r.choice(cases["max_independent"]);cover=[i for i in range(10) if not(indep>>i&1)];r.shuffle(cover);stars={i:[] for i in cover}
 for a,b in E:
  if a in stars and b in stars:
   if r.randrange(2):a,b=b,a
  elif a not in stars:a,b=b,a
  stars[a].append(b)
 g=[];outs=[]
 for a,ns in stars.items():
  assert ns;r.shuffle(ns);w=ns[0]
  for b in ns[1:]:g.append([1,w,b]);w=10+len(g)-1
  g.append([0,a,w]);outs.append(10+len(g)-1)
 r.shuffle(outs)
 while len(outs)>1:
  i=r.randrange(len(outs));a=outs.pop(i);i=r.randrange(len(outs));b=outs.pop(i)
  g.append([1,a,b]);outs.append(10+len(g)-1)
 assert len(g)==20 and ev(g)[0]==0
 return g

def smaller():
 base=baseline();d=r.randrange(len(base));repl=base[d][r.randrange(1,3)];gone=10+d
 def remap(i):return repl if i==gone else i-1 if i>gone else i
 return [[o,remap(a),remap(b)] for j,(o,a,b) in enumerate(base) if j!=d]

start=time.monotonic();it=0;best=999;last=start;restarts=0
while time.monotonic()-start<args.seconds:
 g=smaller();score,_,_=ev(g);stale=0;restarts+=1
 for local in range(50000):
  it+=1;stale+=1
  if time.monotonic()-start>=args.seconds:break
  changed=[]
  for k in range(1 if r.random()<0.92 else r.randrange(2,5)):
   i=r.randrange(len(g));j=r.randrange(3);old=g[i][j];g[i][j]=r.randrange(2) if j==0 else r.randrange(10+i);changed.append((i,j,old))
  new,y,v=ev(g)
  temperature=0.18*(1-local/50000)+0.015
  if new<=score or (r.random()<math.exp(min(0,(score-new)/temperature))):
   if new<score:stale=0
   score=new
  else:
   for i,j,old in reversed(changed):g[i][j]=old
  if score<best:
   best=score;rec={"seed":args.seed,"elapsed":time.monotonic()-start,"iterations":it,"errors":best,"gates":g}
   print(json.dumps(rec),flush=True);(out/"best.json").write_text(json.dumps(rec,indent=2))
  if score==0:
   ok=True;fail=[]
   for s in range(1024):
    v=[bool(s>>i&1) for i in range(10)]
    for o,a,b in g:v.append(v[a] or v[b] if o else v[a] and v[b])
    if v[-1]!=target(s):ok=False;fail.append(s)
   print("FOUND_FULL_VERIFIED",ok,flush=True);(out/"witness.json").write_text(json.dumps({"verified":ok,"gates":g,"failures":fail},indent=2));raise SystemExit(0)
  if time.monotonic()-last>=30:
   last=time.monotonic();print(json.dumps({"elapsed":last-start,"iterations":it,"restarts":restarts,"best":best}),flush=True)
print(json.dumps({"finished":True,"elapsed":time.monotonic()-start,"iterations":it,"restarts":restarts,"best":best}),flush=True)
