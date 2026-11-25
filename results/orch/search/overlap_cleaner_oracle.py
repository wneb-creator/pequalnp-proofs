from pathlib import Path
import json,time
n=6;inputs=[sum(1<<x for x in range(64) if x>>i&1) for i in range(6)]
OR=[sum(1<<x for x in range(64) if x&s) for s in range(64)]
products=[(p,q,OR[p]&OR[q]) for p in range(64) for q in range(p,64)]
counts={'graphs':0,'arm_pairs':0,'overlap_at_least_two':0,'singleton_overlap_large_arms':0,'singleton_arm':0,'guarded_edge_checks':0}
start=time.time()
for mask in range(512):
 if any(sum(bool(mask>>(3*a+j)&1 and mask>>(3*b+j)&1) for j in range(3))>1 for a in range(3) for b in range(a+1,3)):continue
 edges=[(i,j+3) for i in range(3) for j in range(3) if mask>>(3*i+j)&1]
 adj=[0]*6
 for u,v in edges:adj[u]|=1<<v;adj[v]|=1<<u
 F=sum(1<<x for x in range(64) if any(x>>u&1 and x>>v&1 for u,v in edges))
 counts['graphs']+=1
 for p,q,g in products:
  counts['arm_pairs']+=1
  W=sum(1<<w for w in range(6) if not (g&inputs[w]&~F))
  overlap=p&q
  if overlap.bit_count()>=2:
   counts['overlap_at_least_two']+=1
   assert W.bit_count()<=1,('large_overlap',mask,p,q,W)
  if overlap.bit_count()==1 and p.bit_count()>=2 and q.bit_count()>=2:
   counts['singleton_overlap_large_arms']+=1
   r=(overlap&-overlap).bit_length()-1
   T=W&(p|q)
   assert T.bit_count()<=1,('singleton_overlap',mask,p,q,W,T)
   assert T&~adj[r]==0,('nonadjacent_center',mask,p,q,W,T)
   sub=W
   while True:
    Tsub=sub&(p|q);cover=overlap|Tsub
    for u,v in edges:
     pair=(1<<u)|(1<<v)
     if g>>pair&1 and sub&pair:
      counts['guarded_edge_checks']+=1
      assert cover&pair,('uncovered',mask,p,q,sub,u,v)
    if sub==0:break
    sub=(sub-1)&W
  if p.bit_count()<=1 or q.bit_count()<=1:
   counts['singleton_arm']+=1
   arm=p if p.bit_count()<=1 else q
   for u,v in edges:
    pair=(1<<u)|(1<<v)
    if g>>pair&1:
     assert arm&pair,('singleton_arm_uncovered',mask,p,q,u,v)
counts['elapsed_seconds']=time.time()-start
print(json.dumps({'result':'PASS','bounds':'all3+3bipartiteC4freegraphs; allarmsets; allcleanersubsets forsingleton-overlap cover','counts':counts},indent=2))
Path('/tmp/oec/pequalnp-pilot-176/overlap-cleaner-oracle-results.json').write_text(json.dumps(counts,indent=2))
