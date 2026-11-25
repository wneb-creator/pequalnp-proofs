import itertools,json
from pathlib import Path
import cegis_seed_repair as c
base=Path('/tmp/oec/pequalnp-pilot-62');data=json.loads(c.DATA.read_text());w=json.loads((base/'pg3-marginal48-canonical-invalid.json').read_text());bad=set(c.seed_errors(w,data['positive_samples'],data['negative_samples']));good=[i for i in range(468) if i not in bad];edges=set(data['positive_samples']);pairs=[(i,j) for i,j in itertools.combinations(range(26),2) if (1<<i)|(1<<j) not in edges];masks=[(1<<i)|(1<<j) for i,j in pairs]
coverage={i:sum((q&pair==pair)<<b for b,pair in enumerate(masks)) for i in good for q in [data['negative_samples'][i]]}
full=(1<<len(pairs))-1;covered=0;chosen=[];gains=[]
while True:
 available=[i for i in good if i not in chosen]
 if not available:break
 i=max(available,key=lambda j:((coverage[j]&~covered).bit_count(),-j));gain=(coverage[i]&~covered).bit_count()
 if not gain:break
 chosen.append(i);gains.append(gain);covered |= coverage[i]
missing=[pairs[b] for b in range(len(pairs)) if not(covered>>b&1)]
reduced=chosen.copy();changes=[]
while True:
 changed=False
 for i in reduced.copy():
  union=0
  for j in reduced:
   if j!=i:union |= coverage[j]
  if union==covered:
   reduced.remove(i);changes.append({'remove':[i],'add':[]});changed=True;break
 if changed:continue
 for a,b in itertools.combinations(reduced,2):
  union=0
  for j in reduced:
   if j not in [a,b]:union |= coverage[j]
  replacement=next((j for j in good if j not in reduced and union|coverage[j]==covered),None)
  if replacement is not None:
   reduced.remove(a);reduced.remove(b);reduced.append(replacement)
   changes.append({'remove':[a,b],'add':[replacement]});changed=True;break
 if not changed:break
assert all(i in good for i in reduced)
check=0
for i in reduced:check |= coverage[i]
assert check==covered
result={'good_seed_rows':good,'nonedge_pairs':len(pairs),'covered_pairs':covered.bit_count(),'missing_pairs':missing,'greedy_rows':chosen,'new_pair_gains':gains,'selected_count':len(chosen),'reduced_cover_rows':sorted(reduced),'reduced_count':len(reduced),'cover_reductions':changes,'scope':'Greedy cover of nonedge pairs by generic rows already rejected by INVALID48 seed; no optimality claim'}
(base/'marginal-good-row-pair-cover.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k not in ['good_seed_rows','missing_pairs','scope']});print('missing_pairs',missing)
