import itertools,json,time
n=6;N=1<<n;full=(1<<N)-1
xs=[sum(1<<x for x in range(N) if x>>v&1) for v in range(n)]
ors=[sum(1<<x for x in range(N) if x&s) for s in range(N)]
edges=[(a,b) for a in range(3) for b in range(3,6)]
left=[s for s in range(1,8) if s.bit_count()>=2]
right=[s<<3 for s in left]
start=time.time();checked=0;flags=0
for gm in range(1,1<<len(edges)):
 E=[e for i,e in enumerate(edges) if gm>>i&1]
 if any(sum((a,c) in E and (b,c) in E for c in range(3,6))>=2 for a in range(3) for b in range(a+1,3)):continue
 F=0
 for a,b in E:F|=xs[a]&xs[b]
 neg=full^F;rows=[((a,b),1<<((1<<a)|(1<<b))) for a,b in E]
 for P in left:
  for Q in right:
   g=ors[P]&ors[Q]
   if not(g&neg):continue
   wg={w for w in range(n) if not(g&xs[w]&neg)}
   if not(any(P>>w&1 for w in wg) and any(Q>>w&1 for w in wg)):continue
   flags+=1
   for S in range(1,N):
    h=g&ors[S]
    if h==g or not(h&neg):continue
    wh={w for w in range(n) if not(h&xs[w]&neg)}
    if not(wh-wg):continue
    gamma=[e for e,row in rows if h&row]
    checked+=1
    if len(gamma)<2 or set.intersection(*(set(e) for e in gamma)):continue
    print(json.dumps({'n':n,'edges':E,'P':[v for v in range(n) if P>>v&1],'Q':[v for v in range(n) if Q>>v&1],'S':[v for v in range(n) if S>>v&1],'Wg':sorted(wg),'Wh':sorted(wh),'gamma_h':gamma,'seconds':time.time()-start,'tested':checked,'flags':flags}),flush=True);raise SystemExit
print(json.dumps({'none':True,'seconds':time.time()-start,'tested':checked,'flags':flags}),flush=True)
