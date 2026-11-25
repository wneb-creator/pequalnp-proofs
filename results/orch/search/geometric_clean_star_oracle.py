from pathlib import Path
from itertools import combinations
import argparse,json,time
parser=argparse.ArgumentParser();parser.add_argument('--max-n',type=int,default=6);parser.add_argument('--stop-first',action='store_true');parser.add_argument('--no-isolates',action='store_true');parser.add_argument('--wide-arms',action='store_true');parser.add_argument('--connected',action='store_true');parser.add_argument('--tag',default='');parser.add_argument('--disjoint-arms',action='store_true');args=parser.parse_args()
start=time.time();stats={'graphs':0,'dirty_products':0,'safe_nonlowerable_pairs':0};first={};allfound=[]
def vertices(mask,n):return [i for i in range(n) if mask>>i&1]
def record(p,n,edges):
 return {'arms':[vertices(p['p'],n),vertices(p['q'],n)],'wmax':vertices(p['w'],n),'accepted_edges':[e for k,e in enumerate(edges) if p['es']>>k&1],'guarded_edges':[e for k,e in enumerate(edges) if p['guard']>>k&1],'clean_star_centers':vertices(p['centers'],n),'flag_centers':p['flags']}
for n in range(2,args.max_n+1):
 rows=range(1<<n);inputs=[sum(1<<x for x in rows if x>>i&1) for i in range(n)];ors=[sum(1<<x for x in rows if x&p) for p in range(1<<n)]
 products=[(p,q,ors[p]&ors[q]) for p in range(1,1<<n) for q in range(p+1,1<<n) if p&q not in [p,q]]
 for left in range(1,n//2+1):
  potential=[(i,j) for i in range(left) for j in range(left,n)]
  graphmasks=sorted(range(1,1<<len(potential)),key=int.bit_count)
  for mask in graphmasks:
   edges=[e for i,e in enumerate(potential) if mask>>i&1];adj=[0]*n
   for u,v in edges:adj[u]|=1<<v;adj[v]|=1<<u
   if args.no_isolates and any(a==0 for a in adj):continue
   if args.connected:
    reached=1
    while True:
     extended=reached
     for v in vertices(reached,n):extended|=adj[v]
     if extended==reached:break
     reached=extended
    if reached!=(1<<n)-1:continue
   if any((adj[a]&adj[b]).bit_count()>1 for a in range(n) for b in range(a+1,n)):continue
   stats['graphs']+=1;F=sum(1<<x for x in rows if any(x>>u&1 and x>>v&1 for u,v in edges));bad=[]
   for p,q,g in products:
    if args.disjoint_arms and p&q:continue
    if args.wide_arms and min(p.bit_count(),q.bit_count())<2:continue
    dirty=g&~F
    if not dirty:continue
    stats['dirty_products']+=1
    w=sum(1<<i for i in range(n) if not (dirty&inputs[i]));es=sum(1<<k for k,(u,v) in enumerate(edges) if g>>((1<<u)|(1<<v))&1)
    centers=0;flags=[]
    for a,b in [(p,q),(q,p)]:
     for z in vertices(a,n):
      if b&~adj[z]:continue
      if all(z in edges[k] for k in range(len(edges)) if es>>k&1):centers|=1<<z
    if not p&q and p.bit_count()>=2 and q.bit_count()>=2:
     flags=[(z,zp) for z in vertices(p,n) for zp in vertices(q,n) if adj[z]>>zp&1 and not(p&~adj[zp]) and not(q&~adj[z])]
    if centers:continue
    guard=sum(1<<k for k,(u,v) in enumerate(edges) if es>>k&1 and w&((1<<u)|(1<<v)))
    bad.append({'p':p,'q':q,'g':g,'d':dirty,'w':w,'es':es,'guard':guard,'centers':centers,'flags':flags})
   for i,g in enumerate(bad):
    for h in bad[i+1:]:
     if g['d']&h['d'] or (g['flags'] and h['flags']):continue
     stats['safe_nonlowerable_pairs']+=1
     common=g['es']&h['es'];tests={'bare':True,'common_edge':bool(common),'both_nonempty_wmax':bool(g['w'] and h['w']),'both_guarded_nonempty':bool(g['guard'] and h['guard']),'both_guarded_and_common':bool(g['guard'] and h['guard'] and common),'union_covers_graph':bool((g['es']|h['es'])==(1<<len(edges))-1),'both_guarded_union_graph':bool(g['guard'] and h['guard'] and (g['es']|h['es'])==(1<<len(edges))-1)}
     for label,yes in tests.items():
      if not yes or label in first:continue
      item={'label':label,'n':n,'left_size':left,'edges':edges,'g':record(g,n,edges),'h':record(h,n,edges),'shared_edges':[e for k,e in enumerate(edges) if common>>k&1],'dirty_witnesses':[next(x for x in rows if a['d']>>x&1) for a in [g,h]],'truth_table_clean':not bool(g['g']&h['g']&~F)}
      first[label]=item;allfound.append(item);print(json.dumps(item),flush=True)
   if args.stop_first and 'both_guarded_and_common' in first:break
  if args.stop_first and 'both_guarded_and_common' in first:break
 if args.stop_first and 'both_guarded_and_common' in first:break
 print(json.dumps({'completed_n':n,'stats':stats,'first_labels':list(first)}),flush=True)
out={'first_witnesses':first,'stats':stats,'elapsed_seconds':time.time()-start,'max_n_requested':args.max_n,'no_isolates':args.no_isolates,'wide_arms':args.wide_arms,'connected':args.connected,'disjoint_arms':args.disjoint_arms,'stopped_at_first':args.stop_first}
Path('/tmp/oec/pequalnp-pilot-176/geometric-clean-star'+args.tag+'-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'final':out['stats'],'elapsed_seconds':out['elapsed_seconds']}),flush=True)
