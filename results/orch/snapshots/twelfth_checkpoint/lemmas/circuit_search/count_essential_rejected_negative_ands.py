"""Diagnostic counts on maximal negatives rejected by the approximate output."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
summary=[]
for tag,n,test_path,pool_path in [('five',52,HERE.parent/'algebra_strategy'/'five-owner-joint-packet.json',HERE/'joint5essential-pool.json'),('global',26,HERE/'full-case.json',HERE/'globalessential-pool.json')]:
 c=json.loads(test_path.read_text());c=c[0] if isinstance(c,list) else c;tests=c['tests'];target=sum(y<<j for j,(_,y) in enumerate(tests));allbits=(1<<len(tests))-1;cols=[sum((m>>i&1)<<j for j,(m,_) in enumerate(tests)) for i in range(n)]
 pool=json.loads(pool_path.read_text());out=[]
 for idx,x in enumerate(pool):
  g=x['gates'];v=cols.copy()
  for op,a,b in g:v.append(v[a]|v[b] if op else v[a]&v[b])
  used={n+len(g)-1}
  for i in range(len(g)-1,-1,-1):
   if n+i in used:used.update(g[i][1:])
  rejected=allbits&~target&~v[-1];dirty=[];essential=[];critical=[];losses={}
  for i,(op,a,b) in enumerate(g):
   if op or a==b or n+i not in used or not(v[n+i]&rejected):continue
   dirty.append(i)
   if not(v[n+i]&target):continue
   good=True
   for replacement in [a,b,None]:
    w=v.copy();w[n+i]=0 if replacement is None else v[replacement]
    for j in range(i+1,len(g)):
     op2,l,r=g[j];w[n+j]=w[l]|w[r] if op2 else w[l]&w[r]
    if replacement is None:losses[str(i)]=(target&v[-1]&~w[-1]).bit_count()
    if w[-1]==v[-1]:good=False;break
   if good:
    essential.append(i)
    if losses.get(str(i),0)>=2:critical.append(i)
  out.append(dict(index=idx,errors=(v[-1]&~target).bit_count(),active_and=x['active_and'],rejected_negative_dirty_ands=dirty,essential_rejected_negative_dirty_ands=essential,positive_loss_by_essential_junk=losses,two_edge_critical_junk=critical))
 (HERE/f'{tag}-essential-rejected-negative-census-source.json').write_text(json.dumps(pool))
 (HERE/f'{tag}-essential-rejected-negative-census.json').write_text(json.dumps(out))
 s=dict(case=tag,models=len(out),best_by_minimum_junk={str(k):min((x['errors'] for x in out if len(x['essential_rejected_negative_dirty_ands'])>=k),default=None) for k in [0,1,2,3]},best_two_critical_junk=min((x['errors'] for x in out if len(x['two_edge_critical_junk'])>=2),default=None));summary.append(s);print(s)
(HERE/'essential-rejected-negative-census-summary.json').write_text(json.dumps(summary,indent=2))
