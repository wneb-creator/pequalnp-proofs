from pathlib import Path
from itertools import combinations
import json,time,argparse
p=argparse.ArgumentParser();p.add_argument('--max-n',type=int,default=6);p.add_argument('--tag',default='');args=p.parse_args();started=time.time();counts={'graphs':0,'g_singleton_two_center':0,'guarded_matching_pairs':0};found=None
for n in range(2,args.max_n+1):
 rows=range(1<<n);ors=[sum(1<<x for x in rows if x&a) for a in range(1<<n)];products=[(a,b,ors[a]&ors[b]) for a in range(1,1<<n) for b in range(a+1,1<<n) if a&b not in [a,b] and min(a.bit_count(),b.bit_count())>=2]
 for left in range(1,n//2+1):
  possible=[(i,j) for i in range(left) for j in range(left,n)]
  for em in sorted(range(1,1<<len(possible)),key=int.bit_count):
   edges=[e for k,e in enumerate(possible) if em>>k&1];adj=[0]*n
   for u,v in edges:adj[u]|=1<<v;adj[v]|=1<<u
   if not all(adj) or any((adj[i]&adj[j]).bit_count()>1 for i in range(n) for j in range(i+1,n)):continue
   counts['graphs']+=1;F=sum(1<<x for x in rows if any(x>>u&1 and x>>v&1 for u,v in edges));prods=[]
   for a,b,val in products:
    dirty=val&~F
    if dirty:prods.append((a,b,val,dirty,sum(1<<k for k,(u,v) in enumerate(edges) if val>>((1<<u)|(1<<v))&1)))
   for P,Q,g,gd,ges in prods:
    if (P&Q).bit_count()!=1:continue
    r=(P&Q).bit_length()-1;W=sum(1<<v for v in range(n) if not(gd&ors[1<<v]));T=W&(P|Q)
    if T.bit_count()!=1:continue
    t=T.bit_length()-1;guard=sum(1<<k for k,(u,v) in enumerate(edges) if ges>>k&1 and W&((1<<u)|(1<<v)))
    matches=[(1<<i)|(1<<j) for i,j in combinations(range(len(edges)),2) if guard>>i&1 and guard>>j&1 and len(set(edges[i]+edges[j]))==4]
    if not matches:continue
    counts['g_singleton_two_center']+=1
    for R,S,h,hd,hes in prods:
     if gd&hd or not any(hes&mm==mm for mm in matches):continue
     counts['guarded_matching_pairs']+=1
     badL=g&ors[R]&~F;badR=g&ors[S]&~F
     if not badL or not badR:continue
     verts=lambda a:[i for i in range(n) if a>>i&1]
     found={'n':n,'edges':edges,'g_arms':[verts(P),verts(Q)],'h_arms':[verts(R),verts(S)],'r':r,'t':t,'wmax_g':verts(W),'guarded_shared_edges':[e for k,e in enumerate(edges) if guard>>k&1 and hes>>k&1],'joint_clean':True,'left_triple_negative':next(x for x in rows if badL>>x&1),'right_triple_negative':next(x for x in rows if badR>>x&1),'g_accepts_all_graph_edges':ges==(1<<len(edges))-1,'g_guards_all_graph_edges':guard==(1<<len(edges))-1}
     print(json.dumps({'counterexample':found}),flush=True);break
    if found:break
   if found:break
  if found:break
 if found:break
 print(json.dumps({'completed_n':n,'counts':counts,'elapsed_seconds':time.time()-started}),flush=True)
result={'counterexample':found,'counts':counts,'elapsed_seconds':time.time()-started,'max_n_requested':args.max_n};Path('/tmp/oec/pequalnp-pilot-176/geometric-guarded-matching'+args.tag+'-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
