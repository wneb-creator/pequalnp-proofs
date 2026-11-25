from pathlib import Path
import importlib.util,random,json,hashlib,datetime,copy
src=Path('/tmp/oec/pequalnp-pilot-121/andcount2056/andcount_budget_profile2056.py');spec=importlib.util.spec_from_file_location('profile',src);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
edges,rows=m.geometry();P=(1<<52)-1;ALL=(1<<756)-1;N=ALL^P;rng=random.Random(20561821);cleared=atomic=trials=0;strict=0
for trial in range(600):
 K=1+trial%20;records=[]
 for j in range(K):
  if rng.randrange(6)==0:records.append({'left':[],'right':[]});continue
  records.append({key:sorted(rng.sample(range(26+j),rng.randint(1,3))) for key in ('left','right')})
 model={'ands':records,'output':sorted(rng.sample(range(K),rng.randint(1,K)))};oldvals,oldout=m.evaluate(model,rows);newvals=oldvals[:26];newrecords=[]
 for j,rec in enumerate(records):
  profile=oldvals[26+j]&P
  if not profile:
   q={'left':[],'right':[]};cleared+=int(bool(rec['left']))
  elif profile.bit_count()==1:
   e=edges[profile.bit_length()-1];q={'left':[e[0]],'right':[e[1]]};atomic+=1
  else:q=copy.deepcopy(rec)
  left=right=0
  for i in q['left']:left|=newvals[i]
  for i in q['right']:right|=newvals[i]
  val=left&right;assert val&P==profile and not(val&N&~oldvals[26+j]);newvals.append(val);newrecords.append(q)
 new={'ands':newrecords,'output':model['output']};_,newout=m.evaluate(new,rows);assert newout&P==oldout&P and not(newout&N&~oldout)
 cost=lambda model:sum(len(r['left'])+len(r['right']) for r in model['ands'])+len(model['output'])-sum(bool(r['left']) for r in model['ands'])-1
 assert cost(new)<=cost(model);strict+=int(cost(new)<cost(model));ordinary=m.materialize(new);assert m.ordinary_eval(ordinary,rows)==newout and ordinary['size']<=cost(new)
 for j,rec in enumerate(newrecords):
  prof=newvals[26+j]&P;assert bool(rec['left'])==bool(prof) and bool(rec['left'])==bool(rec['right'])
  if prof.bit_count()==1:
   e=edges[prof.bit_length()-1];assert rec=={'left':[e[0]],'right':[e[1]]}
 trials+=1
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'status':'PASS normalization semantics and membership bound','models':trials,'rows_per_model':756,'active_zero_profile_clearings':cleared,'singleton_replacements':atomic,'strict_cost_decreases':strict,'positive_wire_profiles_preserved':True,'negative_wire_values_never_increased':True,'active_implies_nonzero_profile':True,'singleton_profiles_direct_edges':True,'no_first_AND_anchor':True}
Path('/tmp/oec/pequalnp-pilot-121/not-elimination/andbudget-profile-control.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
