from pathlib import Path
import json,sys,time,heapq,itertools
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
tags={};line_points={};value_index={v:i for i,v in enumerate(fixed)}
for li,line in enumerate(l for l in range(13) if l not in theta_lines):
 xs=[(line+d)%13 for d in [0,1,3,9]];line_points[line]=frozenset(xs)
 tags[26+4*li]=(line,frozenset(xs[:2]));tags[27+4*li]=(line,frozenset(xs[:3]))
 for size in [2,3]:
  for subset in itertools.combinations(xs,size):
   value=fixed[subset[0]]
   for q in subset[1:]:value=combine('or',value,fixed[q])
   if value in value_index:idx=value_index[value]
   else:idx=len(fixed);fixed.append(value);value_index[value]=idx
   tags[idx]=(line,frozenset(subset))
def requirements(state):
 req={}
 for _,src in state:
  if src in tags:
   line,sub=tags[src];req.setdefault(line,set()).add(sub)
 for subs in req.values():
  if len(subs)>2:return None
  if len(subs)==2:
   a,b=list(subs)
   if not(a<=b or b<=a or a.isdisjoint(b)):return None
 return req
unique={v:i for i,v in reversed(list(enumerate(fixed)))};sources=list(unique.values())

def evaluate(state):
 if requirements(state) is None:return None
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
actions=[];singles=[];single_union=0
for port,old in enumerate(baseval[2]):
 for src in sources:
  sv=fixed[src]
  if (sv[0]|old[0])==old[0] and (sv[1]|old[1])==old[1] and (sv[2]|old[2])==old[2]:continue
  state=((port,src),);val=evaluate(state)
  if val is None:continue
  actions.append((port,src));singles.append((val[0].bit_count(),port,src));single_union |= baseval[0]&~val[0]
missing_positions=[i for i in range(len(rows)) if baseval[0]>>i&1]
source_masks=set()
for _,src in actions:
 mask=0
 if not 13<=src<26:
  for b,r in enumerate(missing_positions):
   if fixed[src][0]>>r&1:mask |= 1<<b
 source_masks.add(mask)
reach={0};cover_lower_bound=99
for number in range(1,len(missing_positions)+1):
 reach |= {r|m for r in list(reach) for m in source_masks}
 if (1<<len(missing_positions))-1 in reach:cover_lower_bound=number;break
print(json.dumps({'safe_actions':len(actions),'single_covered':single_union.bit_count(),'source_cover_lower_bound':cover_lower_bound,'largest_source_cover':max(map(int.bit_count,source_masks)),'best_singles':sorted(singles)[:30]}),flush=True)
if cover_lower_bound>7:
 print('OR-INJECTION LOWER BOUND',cover_lower_bound,flush=True)
 (base/('theta-virtual-actions-'+Path(sys.argv[1]).stem+'.json')).write_text(json.dumps({'singles':singles,'actions':actions,'prefix':prefix,'embedding':embedding,'source_masks':list(source_masks),'source_cover_lower_bound':cover_lower_bound},indent=2)+'\n')
 sys.exit(0)
beam=[((),baseval)];seen={hash(baseval[1]):0};found=None
for depth in range(1,8):
 candidates={};tested=0
 for state,_ in beam:
  for action in actions:
   if action in state:continue
   ns=tuple(sorted(state+(action,)));val=evaluate(ns);tested+=1
   if val is None:continue
   sig=hash(val[1])
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
 req=requirements(found);circuit=[];newvals=fixed[:26];available={v:i for i,v in enumerate(newvals)};newroots=[]
 def addgate(op,a,b):
  circuit.append((op,a,b));value=combine(op,newvals[a],newvals[b]);newvals.append(value);available[value]=26+len(circuit)-1;return 26+len(circuit)-1
 for line in sorted(line_points):
  points=line_points[line];subs=sorted(req.get(line,set()),key=lambda x:(len(x),sorted(x)))
  if len(subs)==2 and subs[0].isdisjoint(subs[1]):
   a,b=sorted(subs[0]);left=addgate('or',a,b);a,b=sorted(subs[1]);right=addgate('or',a,b);root=addgate('or',left,right)
  else:
   if subs:
    first=sorted(subs[0])[:2];order=first
    if len(subs[-1])==3:order += sorted(subs[-1]-set(order))
    order += sorted(points-set(order))
   else:order=sorted(points)
   root=order[0]
   for q in order[1:]:root=addgate('or',root,q)
  newroots.append(addgate('and',13+line,root))
 newg=newroots[0]
 for root in newroots[1:]:newg=addgate('or',newg,root)
 assert len(circuit)==39
 remap={src:available[fixed[src]] for _,src in found};mapping=embedding[:]

 for j,(op,a,b) in enumerate(theta):
  pair=[]
  for p,i in enumerate([a,b]):
   w=mapping[i]
   for key,src in found:
    if key==2*j+p:
     source=remap[src]
     if w!=source:circuit.append(('or',w,source));w=26+len(circuit)-1
   pair.append(w)
  circuit.append((op,*pair));mapping.append(26+len(circuit)-1)
 circuit.append(('or',newg,mapping[seed['output']]));out=26+len(circuit)-1
 report={'gates':circuit,'output':out,'size':len(circuit),'state':found,'embedding':embedding}
 (base/('theta-extended-virtual-'+Path(sys.argv[1]).stem+'.json')).write_text(json.dumps(report,indent=2)+'\n')
 print('FULL SIZE',len(circuit),flush=True)
else:print('NO WITNESS',time.monotonic()-start,flush=True)
(base/('theta-virtual-actions-'+Path(sys.argv[1]).stem+'.json')).write_text(json.dumps({'singles':singles,'actions':actions,'prefix':prefix,'embedding':embedding},indent=2)+'\n')
