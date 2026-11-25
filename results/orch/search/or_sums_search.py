import random,time,json,pathlib,sys
D=pathlib.Path('/tmp/oec/pequalnp-pilot-64')
seed=int(sys.argv[1]); seconds=int(sys.argv[2]); rng=random.Random(seed)
n=13; size=38; allbits=(1<<(1<<n))-1
inputs=[sum(1<<a for a in range(1<<n) if (a>>i)&1) for i in range(n)]
sets=[[p for p in range(n) if (p-l)%n in (0,1,3,9)] for l in range(n)]
targets=[sum(1<<a for a in range(1<<n) if any((a>>p)&1 for p in s)) for s in sets]
def star():
 gs=[]
 for s in rng.sample(sets,len(sets)):
  s=rng.sample(s,len(s)); w=s[0]
  for p in s[1:]: gs.append((0,w,p)); w=n+len(gs)-1
 return gs

def trim(gs):
 j=rng.randrange(len(gs)); g=gs[j]; replace=rng.choice(g[1:])
 def rewire(x): return replace if x==n+j else x-1 if x>n+j else x
 out=[]
 for k,g in enumerate(gs):
  if k==j:continue
  a,b=rewire(g[1]),rewire(g[2])
  if a==b: b=(b+1)%(n+len(out))
  out.append((g[0],a,b))
 return out

def assess(gs):
 vals=inputs.copy()
 for op,a,b in gs: vals.append(vals[a]&vals[b] if op else vals[a]|vals[b])
 ds=[]; outs=[]
 for tar in targets:
  d,o=min(((tar^v).bit_count(),i) for i,v in enumerate(vals))
  ds.append(d); outs.append(o)
 return sum(ds),ds,outs
start=time.monotonic(); end=start+seconds; best=10**20; it=0; restarts=0
while time.monotonic()<end:
 gs=trim(star()); score,ds,outs=assess(gs); stalled=0; restarts+=1
 while stalled<5000 and time.monotonic()<end:
  it+=1; trial=gs.copy(); edits=1 if rng.random()<.96 else 2
  for _ in range(edits):
   j=rng.randrange(size); op,a,b=trial[j]; typ=rng.randrange(10)
   if typ==0: op=1-op
   elif typ<5:a=rng.randrange(n+j)
   else:b=rng.randrange(n+j)
   if a==b: b=(b+1)%(n+j)
   trial[j]=(op,a,b)
  sc,dd,oo=assess(trial)
  if sc<best:
   best=sc
   rec=dict(seed=seed,seconds=time.monotonic()-start,iterations=it,score=sc,distances=dd,outputs=oo,gates=trial)
   (D/('or-sums-best-'+str(seed)+'.json')).write_text(json.dumps(rec))
   print(json.dumps({k:v for k,v in rec.items() if k!='gates'}),flush=True)
  if sc==0:
   print('EXACT MULTIOUTPUT WITNESS',flush=True);sys.exit(0)
  if sc<score or sc==score and rng.random()<.25 or rng.random()<.0001:
   if sc<score:stalled=0
   gs,score,ds,outs=trial,sc,dd,oo
  stalled+=1
print(json.dumps(dict(done=True,iterations=it,restarts=restarts,best=best,seconds=time.monotonic()-start)),flush=True)
