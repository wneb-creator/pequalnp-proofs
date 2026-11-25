import itertools,json,time
n=5
N=1<<n
full=(1<<N)-1
xs=[sum(1<<x for x in range(N) if x>>v&1) for v in range(n)]
ors=[sum(1<<x for x in range(N) if x&s) for s in range(N)]
edges=[(a,b) for a in range(2) for b in range(2,n)]
start=time.time();checked=0
for gm in range(1,1<<len(edges)):
 E=[e for i,e in enumerate(edges) if gm>>i&1]
 if any(sum((a,c) in E and (b,c) in E for c in range(2,n))>=2 for a in range(2) for b in range(a+1,2)):continue
 F=0
 for a,b in E:F|=xs[a]&xs[b]
 neg=full^F
 rows=[((a,b),1<<((1<<a)|(1<<b))) for a,b in E]
 for P in range(1,N):
  for Q in range(P+1,N):
   g=ors[P]&ors[Q]
   if g in (ors[P],ors[Q]) or not(g&neg):continue
   wg={w for w in range(n) if not(g&xs[w]&neg)}
   for S in range(1,N):
    h=g&ors[S]
    if h in (g,ors[P],ors[Q],ors[S]) or not(h&neg):continue
    wh={w for w in range(n) if not(h&xs[w]&neg)}
    if not(wh-wg):continue
    gamma=[e for e,row in rows if h&row]
    if len(gamma)<2 or set.intersection(*(set(e) for e in gamma)):continue
    guarded=[e for e in gamma if set(e)&(wg|wh)]
    if len(guarded)!=len(gamma):continue
    checked+=1
    print(json.dumps({'n':n,'edges':E,'P':[v for v in range(n) if P>>v&1],'Q':[v for v in range(n) if Q>>v&1],'S':[v for v in range(n) if S>>v&1],'Wg':sorted(wg),'Wh':sorted(wh),'gamma_h':gamma,'seconds':time.time()-start,'tested':checked}),flush=True)
    raise SystemExit
print(json.dumps({'none':True,'seconds':time.time()-start,'tested':checked}),flush=True)
