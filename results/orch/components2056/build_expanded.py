from pathlib import Path
from collections import defaultdict
import hashlib,json,time

here=Path(__file__).resolve().parent
repo=Path('/workspace/pequalnp-proofs/results/orch')
base_text=(here/'v4-library.json').read_text();base=json.loads(base_text)
population_path=repo/'search2056/nested-stratified/final-populations.json'
population_text=population_path.read_text();population=json.loads(population_text)
data=json.loads((repo/'patch2056/full-variable-data.json').read_text())
assert len(population)==148 and len(data['rows'])==756
profiles=[int(s,16) for s in base['profiles']];old_count=len(profiles)
ids={v:i for i,v in enumerate(profiles)};productions=set(map(tuple,base['productions']));old_productions=productions.copy()
goal=base['goal'];target=profiles[goal];assert target==(1<<52)-1
primary=[sum(((r>>i)&1)<<j for j,r in enumerate(data['rows'])) for i in range(26)]
assert primary==profiles[:26]
errors=[];started=time.monotonic()
for record in population:
 values=primary[:];mapping=list(range(26));gs=record['gates']
 for j,(op,a,b) in enumerate(gs):
  assert op in (0,1) and 0<=a<26+j and 0<=b<26+j
  v=(values[a]|values[b]) if op else (values[a]&values[b])
  if v not in ids:ids[v]=len(profiles);profiles.append(v)
  q=ids[v];left,right=sorted((mapping[a],mapping[b]))
  if q>=26 and q not in (left,right):productions.add((q,op,left,right))
  values.append(v);mapping.append(q)
 output=record['output'];assert 0<=output<len(values)
 errors.append((values[output]^target).bit_count())
after_observed=len(productions)
clean=[i for i,v in enumerate(profiles) if v!=target and not(v>>52)]
for ia,a in enumerate(clean):
 for b in clean[ia+1:]:
  if profiles[a]|profiles[b]==target:productions.add((goal,1,a,b))
incoming=defaultdict(list)
for q,op,a,b in productions:incoming[q].append((a,b))
needed=set(range(26));todo=[goal]
while todo:
 q=todo.pop()
 if q in needed:continue
 needed.add(q)
 for a,b in incoming[q]:todo.extend((a,b))
assert set(range(old_count))<=needed
order=list(range(old_count))+sorted(needed-set(range(old_count)));renumber={old:new for new,old in enumerate(order)}
kept=sorted((renumber[q],op,renumber[a],renumber[b]) for q,op,a,b in productions if q in needed)
assert old_productions<=set(kept)
base['profiles']=[format(profiles[q],'0189x') for q in order];base['productions']=[list(t) for t in kept]
base['extension_148']={'base_library_sha256':hashlib.sha256(base_text.encode()).hexdigest(),'population_path':str(population_path),'population_sha256':hashlib.sha256(population_text.encode()).hexdigest(),'records':len(population),'retains_all_base_profiles_and_productions':True}
(here/'v5-library.json').write_text(json.dumps(base,separators=(',',':'))+'\n')
summary={'old_profiles':old_count,'old_productions':len(old_productions),'records':len(population),'min_error':min(errors),'exact_records':errors.count(0),'all_profiles':len(profiles),'retained_profiles':len(order),'observed_new_productions':after_observed-len(old_productions),'root_or_added':len(productions)-after_observed,'retained_productions':len(kept),'clean_candidates':len(clean),'seconds':time.monotonic()-started,'library_bytes':(here/'v5-library.json').stat().st_size,'library_sha256':hashlib.sha256((here/'v5-library.json').read_bytes()).hexdigest()}
(here/'v5-build-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)
