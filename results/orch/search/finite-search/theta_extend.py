from pathlib import Path
import json,sys,time,heapq
base=Path('/tmp/oec/pequalnp-pilot-65/finite-search');seed=json.loads(Path(sys.argv[1]).read_text());limit=float(sys.argv[2]);width=int(sys.argv[3]);start=time.monotonic()
embedding=[3,0,12,2,8,25,16,13,20,15];theta=seed['gates'];theta_lines={0,2,3,7,12};prefix=[]
def gate(op,a,b):prefix.append((op,a,b));return 26+len(prefix)-1
roots=[]
for line in range(13):
 if line in theta_lines:continue
 xs=[(line+d)%13 for d in [0,1,3,9]];a=xs[0]
 for b in xs[1:]:a=gate('or',a,b)
 roots.append(gate('and',13+line,a))
g=roots[0]
for b in roots[1:]:g=gate('or',g,b)
edges=[(i,j) for i in range(13) for j in range(13) if(i-j)%13 in[0,1,3,9]]
pos=[(1<<i)|(1<<(13+j)) for i,j in edges];neg=json.loads((base/'plane-maxind.json').read_text());rows=[1,1<<13]+pos+neg;target=sum(1<<i for i in range(2,54));badmask=((1<<len(rows))-1)^target
fixed=[(sum(1<<r for r,s in enumerate(rows) if s>>i&1),int(i==13),int(i==0)) for i in range(26)]
def combine(op,a,b):
 av,ax,ay=a;bv,bx,by=b
 if op=='or':return av|bv,ax|bx,ay|by
 return av&bv,(av&1)&bx|ax&(bv&1),((av>>1)&1)&by|ay&((bv>>1)&1)
for op,a,b in prefix:fixed.append(combine(op,fixed[a],fixed[b]))
unique={v:i for i,v in reversed(list(enumerate(fixed)))};sources=list(unique.values())

def evaluate(state):
 ws=[fixed[i] for i in embedding];ports=[]
 for j,(op,a,b) in enumerate(theta):
  pair=[]
  for p,i in enumerate([a,b]):
   val=ws[i];ports.append(val)
   for key,src in state:
    if key==2*j+p:val=combine('or',val,fixed[src])
   pair.append(val)
  ws.append(combine(op,*pair))
 out=combine('or',fixed[g],ws[seed['output']]);v,dx,dy=out
 if v&badmask or dx or dy:return None
 missing=target&~v
 return missing,tuple(ws[10:]),tuple(ports)
baseval=evaluate(())
assert baseval is not None
print(json.dumps({'prefix':len(prefix),'theta':len(theta),'base_gates':len(prefix)+len(theta)+1,'missing':baseval[0].bit_count(),'source_count':len(sources)}),flush=True)
actions=[];singles=[]
for port,old in enumerate(baseval[2]):
 for src in sources:
  sv=fixed[src]
  if (sv[0]|old[0])==old[0] and (sv[1]|old[1])==old[1] and (sv[2]|old[2])==old[2]:continue
  state=((port,src),);val=evaluate(state)
  if val is None:continue
  actions.append((port,src));singles.append((val[0].bit_count(),port,src))
print(json.dumps({'safe_actions':len(actions),'best_singles':sorted(singles)[:30]}),flush=True)
beam=[((),baseval)];seen={baseval[1]:0};found=None
for depth in range(1,8):
 candidates={};tested=0
 for state,_ in beam:
  for action in actions:
   if action in state:continue
   ns=tuple(sorted(state+(action,)));val=evaluate(ns);tested+=1
   if val is None:continue
   sig=val[1]
   if sig in seen and seen[sig]<=depth:continue
   seen[sig]=depth
   if val[0]==0:found=ns;break
   if sig not in candidates:candidates[sig]=(ns,val)
  if found:break
  if time.monotonic()-start>limit:break
 if found:
  print('FOUND',json.dumps(found),flush=True);break
 ordered=sorted(candidates.values(),key=lambda item:(item[1][0].bit_count(),item[1][0],item[0]))
 # Round-robin positive-missing patterns preserves alternatives.
 groups={}
 for item in ordered:groups.setdefault(item[1][0],[]).append(item)
 beam=[]
 while len(beam)<width and groups:
  for mask in list(groups):
   beam.append(groups[mask].pop(0))
   if not groups[mask]:del groups[mask]
   if len(beam)>=width:break
 print(json.dumps({'depth':depth,'tested':tested,'candidates':len(candidates),'beam':len(beam),'best_missing':min((v[0].bit_count() for _,v in beam),default=None),'secs':time.monotonic()-start}),flush=True)
 if not beam or time.monotonic()-start>limit:break
if found:
 circuit=prefix[:];mapping=embedding[:]
 for j,(op,a,b) in enumerate(theta):
  pair=[]
  for p,i in enumerate([a,b]):
   w=mapping[i]
   for key,src in found:
    if key==2*j+p:circuit.append(('or',w,src));w=26+len(circuit)-1
   pair.append(w)
  circuit.append((op,*pair));mapping.append(26+len(circuit)-1)
 circuit.append(('or',g,mapping[seed['output']]));out=26+len(circuit)-1
 report={'gates':circuit,'output':out,'size':len(circuit),'state':found,'embedding':embedding}
 (base/'theta-extended-witness.json').write_text(json.dumps(report,indent=2)+'\n')
 print('FULL SIZE',len(circuit),flush=True)
else:print('NO WITNESS',time.monotonic()-start,flush=True)
(base/'theta-safe-actions.json').write_text(json.dumps({'singles':singles,'actions':actions,'prefix':prefix,'embedding':embedding},indent=2)+'\n')
