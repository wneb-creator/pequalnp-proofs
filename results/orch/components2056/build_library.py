import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path

root=Path(__file__).resolve().parent
patch=root.parent/'patch2056'
data_text=(patch/'full-variable-data.json').read_text()
data=json.loads(data_text);rows=data['rows'];n=data['ninputs']
assert n==26 and len(rows)==756 and len(data['positive'])==52
goal=(1<<52)-1
primary=[sum(((row>>i)&1)<<j for j,row in enumerate(rows)) for i in range(n)]
assert len(set(primary))==26
profiles=primary[:];ids={v:i for i,v in enumerate(profiles)}
productions=set();observations=[];seen=set();sources=[];baseline=None
skipped_self=skipped_primary=0

def add(record,source,index):
 global baseline,skipped_self,skipped_primary
 gs=record['gates'];out=record.get('output',n+len(gs)-1)
 key=(tuple(map(tuple,gs)),out)
 if key in seen:return
 seen.add(key);values=primary[:];mapping=list(range(n));chosen={}
 for j,(op,a,b) in enumerate(gs):
  assert op in (0,1) and 0<=a<n+j and 0<=b<n+j
  value=values[a]|values[b] if op else values[a]&values[b]
  if value not in ids:ids[value]=len(profiles);profiles.append(value)
  parent=ids[value];left,right=sorted((mapping[a],mapping[b]))
  production=(parent,op,left,right)
  if parent<n:skipped_primary+=1
  elif parent in (left,right):skipped_self+=1
  else:
   productions.add(production)
   chosen.setdefault(parent,production)
  values.append(value);mapping.append(parent)
 assert 0<=out<len(values)
 observations.append({'source':source,'record':index,'gates':gs,'output':out,'profile':mapping[out],'exact':values[out]==goal})
 if source=='baseline64':
  assert len(gs)==64 and len(chosen)==64 and values[out]==goal
  baseline={'output':mapping[out],'chosen':[list(p) for p in chosen.values()],'topological_profiles':list(chosen)}

add({'gates':data['gates64'],'output':data['output']},'baseline64',0)
for name in ['full-double-star-seeds.json','full-inverse-hoist-seeds.json','full-paired-star-seeds.json','full-reused-dirty-seeds.json','full-nested-dirty-seeds.json']:
 text=(patch/name).read_text();records=json.loads(text);assert isinstance(records,list)
 sources.append({'path':str((patch/name).relative_to(root.parent)),'sha256_at_read':hashlib.sha256(text.encode()).hexdigest(),'records':len(records)})
 for index,record in enumerate(records):add(record,name,index)
for name in ['full-variable-plus-local.stdout','full-variable-wide-local.stdout','full-variable-stratum-local.stdout','full-variable-undominated-local.stdout']:
 text=(patch/name).read_text();lines=text.splitlines()
 if text and not text.endswith('\n'):lines=lines[:-1]
 sources.append({'path':str((patch/name).relative_to(root.parent)),'sha256_at_read':hashlib.sha256(text.encode()).hexdigest(),'complete_records':len(lines)})
 for index,line in enumerate(lines):add(json.loads(line),name,index)
population=root.parent/'search2056/stratified/final-populations.json'
text=population.read_text();records=json.loads(text);assert isinstance(records,list)
sources.append({'path':str(population.relative_to(root.parent)),'sha256_at_read':hashlib.sha256(text.encode()).hexdigest(),'records':len(records)})
for index,record in enumerate(records):add(record,'stratified-final-populations',index)
for name in ['full-combined-near-hits.best.json']:
 add(json.loads((patch/name).read_text()),name,0)

assert baseline is not None
goal_id=ids[goal]
incoming=defaultdict(list)
for p in productions:incoming[p[0]].append(p)
needed=set(range(n));todo=[goal_id]
while todo:
 profile=todo.pop()
 if profile in needed:continue
 needed.add(profile)
 for _,_,a,b in incoming[profile]:todo.extend((a,b))
old_order=list(range(n))+sorted(needed-set(range(n)))
renumber={old:new for new,old in enumerate(old_order)}
kept=sorted((renumber[parent],op,renumber[a],renumber[b]) for parent,op,a,b in productions if parent in needed)
assert all(parent not in (a,b) and parent>=n for parent,op,a,b in kept)
kept_profiles=[profiles[old] for old in old_order]
for parent,op,a,b in kept:
 assert kept_profiles[parent]==(kept_profiles[a]|kept_profiles[b] if op else kept_profiles[a]&kept_profiles[b])
baseline={'output':renumber[baseline['output']],'chosen':[[renumber[parent],op,renumber[a],renumber[b]] for parent,op,a,b in baseline['chosen']],'topological_profiles':[renumber[x] for x in baseline['topological_profiles']]}
assert len(baseline['chosen'])==64
degree=Counter(parent for parent,op,a,b in kept)
library={'version':1,'inputs':n,'row_count':len(rows),'positive_count':52,'goal':renumber[goal_id],'data_sha256':hashlib.sha256(data_text.encode()).hexdigest(),'profiles':[format(v,'0189x') for v in kept_profiles],'productions':[list(p) for p in kept],'baseline64':baseline,'sources':sources}
(root/'library.json').write_text(json.dumps(library,separators=(',',':'))+'\n')
for record in observations:
 old=record.pop('profile');record['output_profile']=renumber.get(old);record['output_profile_hex']=format(profiles[old],'0189x')
(root/'observed-circuits.jsonl').write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in observations))
summary={'observed_unique_circuits':len(observations),'exact_circuits':sum(r['exact'] for r in observations),'all_profiles':len(profiles),'retained_profiles':len(kept_profiles),'noninput_profiles':len(kept_profiles)-n,'all_productions':len(productions),'retained_productions':len(kept),'max_producers_per_profile':max(degree.values()),'goal_producers':degree[renumber[goal_id]],'skipped_self_productions':skipped_self,'skipped_primary_productions':skipped_primary,'baseline_unique_noninputs':64,'library_bytes':(root/'library.json').stat().st_size}
(root/'build-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary),flush=True)
