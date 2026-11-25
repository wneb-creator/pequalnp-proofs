import itertools,json,time
n=5;edges=[(0,1),(1,2),(2,3),(3,4)]
inputs=[sum(1<<x for x in range(1<<n) if (x>>i)&1) for i in range(n)]
prefix=[('or',1,3),('or',1,2),('or',6,4),('or',0,4),('or',8,2),('or',0,3),('or',10,2)]
values=inputs.copy()
for op,u,v in prefix:values.append(values[u]|values[v])
base=tuple(sorted(set([(x,0) for x in values]+[(0,0)])))
target=0
for u,v in edges:target|=inputs[u]&inputs[v]
star_masks=[sum(1<<j for j,(u,v) in enumerate(edges) if c in (u,v)) for c in range(n)]
def edge_mask(value):return sum(1<<j for j,(u,v) in enumerate(edges) if (value>>((1<<u)|(1<<v)))&1)
cache={}
def em(value):
 if value not in cache:cache[value]=edge_mask(value)
 return cache[value]
states={base:()};transitions=0;start=time.monotonic()
print(json.dumps({'n':n,'edges':edges,'prefix':prefix,'base_signals':len(base),'free_false':True,'free_true':False,'max_added_gates':3}),flush=True)
for k in range(1,4):
 nxt={};accepted=0
 for S,hist in states.items():
  SS=set(S)
  for x,y in itertools.combinations_with_replacement(S,2):
   anc=x[1]|y[1]
   for op in ['and','or']:
    transitions+=1
    val=x[0]&y[0] if op=='and' else x[0]|y[0]
    outanc=anc
    if op=='and':
     own=em(val)&~anc
     if not own or not any(own&~star==0 for star in star_masks):continue
     outanc|=em(val)
    q=(val,outanc)
    if q in SS:continue
    accepted+=1
    if val==target:
     print('WITNESS',json.dumps({'added_gates':k,'history':hist+((op,x,y,q),)}),flush=True);raise SystemExit(0)
    if k<3:nxt.setdefault(tuple(sorted(SS|{q})),hist+((op,x,y,q),))
 print(json.dumps({'added_gates':k,'states_examined':len(states),'next_states':len(nxt),'accepted_transitions':accepted,'transitions':transitions,'seconds':time.monotonic()-start}),flush=True);states=nxt
print('NO_VALID_STAR_OWNERSHIP_COMPLETION_WITH_AT_MOST_3_GATES',flush=True)
