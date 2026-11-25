from pathlib import Path
from itertools import combinations
import json,time
n=8;rows=range(1<<n);ors=[sum(1<<x for x in rows if x&a) for a in range(1<<n)];products=[(a,b,ors[a]&ors[b]) for a in range(1,1<<n) for b in range(a+1,1<<n) if a&b not in [a,b] and min(a.bit_count(),b.bit_count())>=2]
graphs={'C8':[(i,(i+1)%8) for i in range(8)],'theta333':[(0,2),(2,3),(3,1),(0,4),(4,5),(5,1),(0,6),(6,7),(7,1)]};results={}
for name,edges in graphs.items():
 started=time.time();F=sum(1<<x for x in rows if any(x>>u&1 and x>>v&1 for u,v in edges));matches=[sum(1<<i for i in ss) for ss in combinations(range(len(edges)),4) if len(set(v for i in ss for v in edges[i]))==8];prods=[]
 for P,Q,val in products:
  dirty=val&~F
  if not dirty:continue
  W=sum(1<<v for v in range(n) if not(dirty&ors[1<<v]));es=sum(1<<k for k,(u,v) in enumerate(edges) if val>>((1<<u)|(1<<v))&1);guard=sum(1<<k for k,(u,v) in enumerate(edges) if es>>k&1 and W&((1<<u)|(1<<v)))
  prods.append((P,Q,val,dirty,W,es,guard))
 hs=[[h for h in prods if h[4]>>r&1 and not((h[0]|h[1])>>r&1)] for r in range(n)];count=0;found=None
 for P,Q,g,gd,W,ges,gguard in prods:
  if (P&Q).bit_count()!=1 or (W&(P|Q)).bit_count()!=1:continue
  r=(P&Q).bit_length()-1;t=(W&(P|Q)).bit_length()-1
  for R,S,h,hd,Wh,hes,hguard in hs[r]:
   if gd&hd:continue
   residual=ges&hes&~(gguard|hguard)
   if not residual:continue
   count+=1;union=gguard|hguard|(ges&hes)
   if not any(union&mm==mm for mm in matches):continue
   vv=lambda x:[i for i in range(n) if x>>i&1];ee=lambda x:[e for k,e in enumerate(edges) if x>>k&1]
   found={'graph':name,'edges':edges,'g_arms':[vv(P),vv(Q)],'h_arms':[vv(R),vv(S)],'r':r,'t':t,'wmax_g':vv(W),'wmax_h':vv(Wh),'residual':ee(residual),'admissible_edges':ee(union),'g_accepted':ee(ges),'h_accepted':ee(hes),'admissible_matching_four':ee(next(mm for mm in matches if union&mm==mm))};print(json.dumps({'counterexample':found}),flush=True);break
  if found:break
 results[name]={'counterexample':found,'eligible_joint_residual_pairs':count,'dirty_products':len(prods),'elapsed_seconds':time.time()-started};print(json.dumps({name:results[name]}),flush=True)
Path('/tmp/oec/pequalnp-pilot-176/geometric-ustar-cover-results.json').write_text(json.dumps(results,indent=2)+'\n')
