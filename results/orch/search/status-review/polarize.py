import json,itertools,time
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-65/status-review')
D=json.loads((p/'bowtie-8-double-1-2.witness.json').read_text());small=D['gates'];n=10
edges=[(a,b+5) for a,b in D['edges']]+[(b,a+5) for a,b in D['edges']]
vals=[sum(1<<r for r in range(1<<n) if r>>i&1) for i in range(n)]
target=0
for a,b in edges:target|=vals[a]&vals[b]
def ev(gs):
 w=vals[:]
 for op,a,b in gs:w.append(w[a]&w[b] if op=='and' else w[a]|w[b])
 return w

def ds(gs,p,q):
 def trace(base,source):
  w=[i==base for i in range(n)];d=[i==source for i in range(n)]
  for op,a,b in gs:
   d.append((w[a] and d[b]) or (d[a] and w[b]) if op=='and' else d[a] or d[b])
   w.append(w[a] and w[b] if op=='and' else w[a] or w[b])
  return d[-1]
 return trace(p,q),trace(q,p)

def countlive(gs):
 live={n+len(gs)-1}
 for j in range(len(gs)-1,-1,-1):
  if n+j in live:live.update(gs[j][1:])
 return len(live-set(range(n)))
valid=[];double=[]
for mask in range(1<<len(small)):
 wires=[(i,i+5) for i in range(5)];gs=[]
 for j,(op,a,b) in enumerate(small):
  c=mask>>j&1;aa=wires[a];bb=wires[b]
  wires.append((n+len(gs),n+len(gs)+1))
  gs.extend([(op,aa[0],bb[c]),(op,aa[1],bb[1-c])])
 gs.append(('or',*wires[-1]))
 if ev(gs)[-1]!=target:continue
 valid.append(mask)
 twice=[e for e in edges if ds(gs,*e)==(False,False)]
 print('valid',mask,'live',countlive(gs),'double',twice,flush=True)
 if twice:
  double.append(mask)
  (p/f'polarized-{mask}.json').write_text(json.dumps(dict(n=n,edges=edges,gates=gs,output=n+len(gs)-1,double_edges=twice),indent=2)+'\n')
print('done valid',len(valid),'double',len(double),flush=True)
