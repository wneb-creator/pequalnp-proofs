from pathlib import Path
import hashlib,json,datetime
s=Path('/tmp/oec/pequalnp-pilot-121/andcount2056');out=Path('/tmp/oec/pequalnp-pilot-121/not-elimination/andbudget-native-independent-audit.json')
E={(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in (0,1,3,9)}
positive={1<<p|1<<l for p,l in E};negative=set()
for pointset in range(8192):
 lines=sum(1<<l for l in range(13) if not any(pointset>>p&1 and (p,13+l) in E for p in range(13)))
 closed=sum(1<<p for p in range(13) if not any(lines>>l&1 and (p,13+l) in E for l in range(13)))
 if pointset==closed:negative.add(pointset|(lines<<13))
assert len(positive)==52 and len(negative)==704
checks=[]
for name in ['budget-native16-fixed64','budget-native16-free464']:
 record=json.loads((s/(name+'.json')).read_text());mapping=json.loads((s/(name+'.mapping.json')).read_text());model=json.loads((s/(name+'.and-model.json')).read_text());ordinary=json.loads((s/(name+'.ordinary.json')).read_text());rows=mapping['rows'];assert len(rows)==756 and set(rows)==positive|negative
 assignment={}
 for line in (s/(name+'.sol')).read_text().splitlines():
  if line.startswith('v '):
   for lit in map(int,line[2:].split()):
    if lit:assignment[abs(lit)]=lit>0
 count=0;header=None
 with (s/(name+'.cnf')).open() as f:
  for line in f:
   if line.startswith('p '):header=list(map(int,line.split()[2:]));continue
   if line.startswith('c ') or not line.strip():continue
   xs=list(map(int,line.split()));assert xs.pop()==0
   assert any(assignment[abs(x)]==(x>0) for x in xs)
   count+=1
 assert count==record['clauses']==header[1] and set(assignment)==set(range(1,header[0]+1))
 flip=set(mapping['flipped_variables']);original={i:(not v if i in flip else v) for i,v in assignment.items()}
 decoded={'ands':[{'left':[i for i,x in enumerate(mapping['left'][j]) if original[x]],'right':[i for i,x in enumerate(mapping['right'][j]) if original[x]]} for j in range(16)],'output':[j for j,x in enumerate(mapping['output']) if original[x]]}
 assert decoded==model
 vals=[sum(bool(r>>i&1)<<k for k,r in enumerate(rows)) for i in range(26)]
 for j,g in enumerate(ordinary['gates']):
  op,a,b=g;assert op in (0,1) and 0<=a<26+j and 0<=b<26+j;vals.append(vals[a]|vals[b] if op else vals[a]&vals[b])
 actual=vals[ordinary['output']];target=sum((r in positive)<<k for k,r in enumerate(rows));assert actual==target
 A=sum(bool(r['left']) for r in model['ands']);M=sum(len(r['left'])+len(r['right']) for r in model['ands'])+len(model['output']);assert A==13 and M==78 and len(ordinary['gates'])==64
 checks.append({'name':name,'clauses_independently_replayed':count,'decoded_memberships_equal':True,'active':A,'memberships':M,'ordinary_size':64,'boundary_errors':0,'cnf_sha256':hashlib.sha256((s/(name+'.cnf')).read_bytes()).hexdigest()})
name='budget-target16-nested';record=json.loads((s/(name+'.json')).read_text());mapping=json.loads((s/(name+'.mapping.json')).read_text());warm=json.loads((s/(name+'.warm.json')).read_text());rows=mapping['rows'];assert len(rows)==756 and set(rows)==positive|negative
vals=[sum(bool(r>>i&1)<<k for k,r in enumerate(rows)) for i in range(26)]
for r in warm['ands']:
 a=b=0
 for i in r['left']:a|=vals[i]
 for i in r['right']:b|=vals[i]
 vals.append(a&b)
value=0
for j in warm['output']:value|=vals[26+j]
misses=[k for k in range(52) if not(value>>k&1)];assert len(misses)==6 and value>>52==0
first_term=max(mapping['output'])+1;expected={tuple(range(first_term+k*16,first_term+(k+1)*16)) for k in misses};fails=[];count=0
with (s/(name+'.cnf')).open() as f:
 for line in f:
  if line.startswith('p ') or line.startswith('c ') or not line.strip():continue
  xs=list(map(int,line.split()));assert xs.pop()==0;count+=1
  if all(x>0 for x in xs):fails.append(tuple(xs))
assert len(fails)==6 and set(fails)==expected and count==record['clauses']
invalid=json.loads((s/'budget-native16-invalid63.json').read_text());assert invalid['exit_code']==20 and invalid['warm_budget_lhs']==81 and invalid['membership_threshold']==80
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verdict':'APPROVED native control artifacts and nested target phase','source_sha256':record['source_sha256'],'controls':checks,'target':{'variables':record['variables'],'clauses':count,'warm_false_constraints':len(fails),'all_failures_exactly_known_positive_misses':True,'missed_row_masks':[rows[k] for k in misses],'budget_lhs':record['warm_budget_lhs'],'budget_rhs':record['membership_threshold'],'cnf_sha256':hashlib.sha256((s/(name+'.cnf')).read_bytes()).hexdigest()},'invalid_fixed_star_cap63':'external UNSAT as expected; not a lower-bound claim'}
out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
