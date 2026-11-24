import importlib.util,json,random,hashlib,time
from pathlib import Path
P=Path('/tmp/oec/pequalnp-pilot-18');source=P/'search_l1342_shard17_ancestorcost.py'
spec=importlib.util.spec_from_file_location('candidate',source);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
started=time.monotonic();rng=random.Random(134217);signed_cases=0
for n in range(7):
 for cap in range(1,n+2):
  for signs in range(1<<n):
   c=m.CNF();base=[c.var() for _ in range(n)];lits=[-v if signs>>i&1 else v for i,v in enumerate(base)];out=m.totalizer_atleast(c,lits,cap)
   for mask in range(1<<n):
    values={v:bool(mask>>i&1) for i,v in enumerate(base)}
    def val(lit):return values.get(abs(lit),False)==(lit>0)
    for clause in c.clauses:
     if all(not val(lit) for lit in clause[:-1]):values[clause[-1]]=True
    count=sum(val(lit) for lit in lits)
    assert [val(lit) for lit in out]==[count>=j for j in range(1,len(out)+1)]
    assert all(any(val(lit) for lit in clause) for clause in c.clauses)
    signed_cases+=1
c=m.CNF();data={'first_junk':17,'lefts':[],'rights':[]}
for g in range(17):
 data['lefts'].append([c.var() for _ in range(13+g)]);data['rights'].append([c.var() for _ in range(13+g)])
oldvars=c.variables;flags=m.prefix_ancestor_flags(c,data);ancestry_cases=0
for trial in range(1024):
 parents=[];values={}
 for g in range(17):
  chosen=[rng.randrange(13+g),rng.randrange(13+g)];parents.append(chosen)
  for row,selection in zip([data['lefts'][g],data['rights'][g]],chosen):values.update({v:i==selection for i,v in enumerate(row)})
 def val(lit):
  if abs(lit) not in values:return None
  return values[abs(lit)]==(lit>0)
 for clause in c.clauses:
  states=[val(lit) for lit in clause]
  if True in states:continue
  unknown=[lit for lit,state in zip(clause,states) if state is None]
  assert unknown
  if len(unknown)==1:values[abs(unknown[0])]=unknown[0]>0
 assert len(values)==c.variables
 assert all(any(val(lit) for lit in clause) for clause in c.clauses)
 expected=[]
 for g in range(17):
  ancestors=set()
  for wire in parents[g]:
   if wire>=13:
    a=wire-13;ancestors.add(a);ancestors.update(expected[a])
  expected.append(ancestors)
  assert [values[v] for v in flags[g]]==[h in ancestors for h in range(g)]
  ancestry_cases+=1
report={'status':'PASS: finite encoder controls; separate math/reviewer verdict required','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'signed_totalizer_assignments':signed_cases,'ancestry_root_checks':ancestry_cases,'ancestor_added_variables':c.variables-oldvars,'ancestor_clauses':len(c.clauses),'seconds':round(time.monotonic()-started,3)}
(P/'ancestorcost-main-validation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
