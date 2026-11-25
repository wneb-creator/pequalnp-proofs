from pathlib import Path
import importlib.util,json,random,hashlib,datetime
base=Path('/tmp/oec/pequalnp-pilot-121');source=base/'andcount2056/andcount_budget_profile_nonread_dirty2056.py'
spec=importlib.util.spec_from_file_location('enc',source);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
edges,_=m.geometry();edge_masks={(1<<a)|(1<<b) for a,b in edges};false_pairs=sorted({(1<<a)|(1<<b) for a in range(26) for b in range(a,26)}-edge_masks);assert len(false_pairs)==299
rng=random.Random(81412056);earliest_checks=0;no_cross=0
for trial in range(600):
 K=rng.randrange(1,20);records=[]
 for j in range(K):
  if rng.randrange(6)==0:records.append({'left':[],'right':[]})
  else:records.append({side:sorted(rng.sample(range(26+j),rng.randrange(1,6))) for side in ['left','right']})
 model={'ands':records,'output':sorted(rng.sample(range(K),rng.randrange(1,K+1)))};values,_=m.evaluate(model,false_pairs);bad=m.bad_primary_crossings(model,edges)
 assert bool(bad)==any(values[26:]);no_cross+=int(not bad)
 for k,row in enumerate(false_pairs):
  first=next((j for j in range(K) if values[26+j]>>k&1),None)
  if first is None:continue
  rec=records[first];lp=[a for a in rec['left'] if a<26 and row>>a&1];rp=[a for a in rec['right'] if a<26 and row>>a&1]
  assert lp and rp and (first,lp[0],rp[0]) in bad;earliest_checks+=1
 for j,a,b in bad:
  index=false_pairs.index((1<<a)|(1<<b));assert values[26+j]>>index&1
star=m.star_model(16,edges);assert not m.bad_primary_crossings(star,edges)
control=json.loads((base/'not-elimination/andbudget-nonread-control67-model.json').read_text());assert m.bad_primary_crossings(control,edges)
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','models':600,'false_pair_rows':299,'earliest_record_checks':earliest_checks,'models_without_bad_crossings':no_cross,'ordered_pair_count':sum((a,b) not in edges and (b,a) not in edges for a in range(26) for b in range(26)),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'test_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(base/'not-elimination/andbudget-dirty-differential.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
