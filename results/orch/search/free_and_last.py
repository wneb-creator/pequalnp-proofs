import itertools,json,time
n=m=3;E=[(0,0),(0,1),(1,1),(1,2),(2,2),(2,0)]
N=n+m;assign=[1<<i for i in range(N)]+[(1<<i)|(1<<j) for i,j in itertools.combinations(range(N),2)]
inp=tuple(sum(1<<k for k,a in enumerate(assign) if (a>>i)&1) for i in range(N))
edgepos=[assign.index((1<<a)|(1<<(n+b))) for a,b in E]
good=sum(1<<k for k in edgepos);allmask=(1<<len(assign))-1;bad=allmask^good
relevant=good|((1<<N)-1)
start=set(inp);start.update(a&b for a in inp for b in inp if (a&b)&relevant)
states={tuple(sorted(start))};t0=time.time()
for r in range(3):
 nxt=set()
 for ws in states:
  old=set(ws)
  for i,a in enumerate(ws):
   for b in ws[i+1:]:
    f=a|b
    if f not in old:nxt.add(tuple(sorted(old|{f}|{f&g for g in ws if (f&g)&relevant})))
 states=nxt
 print(json.dumps({'event':'last_or_build','or_count':r+1,'states':len(states),'elapsed':time.time()-t0}),flush=True)
checked=0;full_contexts=0
for ws in states:
 # Every free-AND signal after one more OR is g AND (u OR v), with g in
 # the old intersection closure, or g=true (no old AND context).
 for g in ws+(allmask,):
  if g&good!=good:continue
  full_contexts+=1
  forbidden=g&bad
  eligible=[u&good for u in ws if not u&forbidden]
  for i,u in enumerate(eligible):
   if any(u|v==good for v in eligible[i:]):
    print('COUNTEREXAMPLE',json.dumps({'signals':ws,'g':g,'u':u,'eligible':eligible,'good':good,'assignments':assign}),flush=True)
    raise SystemExit(1)
 checked+=1
print(json.dumps({'event':'last_or_complete','states_checked':checked,'full_edge_contexts':full_contexts,'or_budget':4,'counterexamples':0,'elapsed':time.time()-t0}),flush=True)
