import json
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-65/status-review')
n=10;vals=[sum(1<<r for r in range(1<<n) if r>>i&1) for i in range(n)]
def norm(gs,out):
 m={i:i for i in range(n)};new=[]
 for j,(op,a,b) in enumerate(gs):
  a,b=m[a],m[b]
  if a==b:m[n+j]=a
  else:m[n+j]=n+len(new);new.append((op,a,b))
 out=m[out];live={out}
 for j in range(len(new)-1,-1,-1):
  if n+j in live:live.update(new[j][1:])
 m={i:i for i in range(n)};small=[]
 for j,(op,a,b) in enumerate(new):
  if n+j in live:m[n+j]=n+len(small);small.append((op,m[a],m[b]))
 return small,m[out]
def evaluate(gs,out):
 w=vals[:]
 for op,a,b in gs:w.append(w[a]&w[b] if op=='and' else w[a]|w[b])
 return w[out]
def trace(gs,out,base,source):
 w=[i==base for i in range(n)];d=[i==source for i in range(n)]
 for op,a,b in gs:
  d.append((w[a] and d[b]) or (d[a] and w[b]) if op=='and' else d[a] or d[b])
  w.append(w[a] and w[b] if op=='and' else w[a] or w[b])
 return d[out]
found=0;cases=[]
for seed in [225,227]:
 D=json.loads((p/f'polarized-{seed}.json').read_text());gs=D['gates'];out=D['output'];target=0
 for a,b in D['edges']:target|=vals[a]&vals[b]
 for j in range(len(gs)):
  for r in range(n+j):
   raw=[]
   for k,(op,a,b) in enumerate(gs):
    if k==j:raw.append(('or',r,r))
    else:raw.append((op,r if a==n+j else a,r if b==n+j else b))
   oo=r if out==n+j else out
   small,oo=norm(raw,oo);z=evaluate(small,oo);bad=(z^target).bit_count();dd=trace(small,oo,1,7)+trace(small,oo,7,1)
   cases.append((bad,dd,len(small),seed,j,r))
   if bad==0 and dd==0:
    found+=1;print('FOUND',cases[-1],flush=True);(p/f'theta-found-{found}.json').write_text(json.dumps(dict(n=n,edges=D['edges'],gates=small,output=oo),indent=2)+'\n')
cases.sort();(p/'drop-polarized-results.json').write_text(json.dumps(cases)+'\n')
print('cases',len(cases),'found',found,'best',cases[:20],flush=True)
