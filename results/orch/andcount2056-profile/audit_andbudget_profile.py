from pathlib import Path
import json,hashlib
base=Path('/tmp/oec/pequalnp-pilot-121/andcount2056')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def evaluate_model(mapping, truth):
 n=mapping['n'];rows=mapping['rows'];vs=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(n)];records=[]
 for j,(ls,rs) in enumerate(zip(mapping['left'],mapping['right'])):
  left=[i for i,x in enumerate(ls) if truth(x)];right=[i for i,x in enumerate(rs) if truth(x)];assert bool(left)==bool(right)
  a=b=0
  for i in left:a|=vs[i]
  for i in right:b|=vs[i]
  v=a&b;records.append({'left':left,'right':right});vs.append(v)
  for k,var in enumerate(mapping['values'][j]):assert truth(var)==bool(v>>k&1)
  positive=v&((1<<52)-1);assert bool(left)==bool(positive)
  if positive.bit_count()==1:
   row=rows[positive.bit_length()-1];ends=[i for i in range(26) if row>>i&1];assert left==[ends[0]] and right==[ends[1]]
 selected=[i for i,x in enumerate(mapping['output']) if truth(x)];out=0
 for i in selected:out|=vs[n+i]
 M=sum(len(r['left'])+len(r['right']) for r in records)+len(selected);A=sum(bool(r['left']) for r in records)
 return records,selected,out,M,A
prefix=base/'profile-native16-free464';mapping=json.loads(prefix.with_suffix('.mapping.json').read_text());meta=json.loads(prefix.with_suffix('.json').read_text());assignment={};sat=False
for line in prefix.with_suffix('.sol').read_text().splitlines():
 if line.startswith('s '):sat=line=='s SATISFIABLE'
 if line.startswith('v '):
  for x in map(int,line.split()[1:]):
   if x:
    assert abs(x) not in assignment or assignment[abs(x)]==(x>0);assignment[abs(x)]=x>0
assert sat and set(assignment)==set(range(1,meta['variables']+1))
count=0
for line in prefix.with_suffix('.cnf').open():
 if line.startswith('p '):assert list(map(int,line.split()[2:]))==[meta['variables'],meta['clauses']];continue
 if line.startswith('c '):continue
 xs=list(map(int,line.split()));assert xs[-1]==0 and any(assignment[abs(x)]==(x>0) for x in xs[:-1]);count+=1
assert count==meta['clauses']
flipped=set(mapping['flipped_variables']);truth=lambda x:assignment[x]^(x in flipped)
records,selected,out,M,A=evaluate_model(mapping,truth);assert out==(1<<52)-1 and M-A-1<=64
saved=json.loads(prefix.with_suffix('.and-model.json').read_text());assert saved=={'ands':records,'output':selected}
net=json.loads(prefix.with_suffix('.ordinary.json').read_text());rows=mapping['rows'];v=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(26)]
for j,(op,a,b) in enumerate(net['gates']):
 assert op in(0,1) and 0<=a<26+j and 0<=b<26+j;v.append(v[a]&v[b] if op==0 else v[a]|v[b])
assert v[net['output']]==out and len(net['gates'])==64
prefix=base/'profile-target16-nested';mapping=json.loads(prefix.with_suffix('.mapping.json').read_text());flipped=set(mapping['flipped_variables']);records,selected,out,M,A=evaluate_model(mapping,lambda x:x in flipped);assert M-A-1==63
bad=[];count=0
for line in prefix.with_suffix('.cnf').open():
 if line.startswith(('p ','c ')):continue
 xs=list(map(int,line.split()));assert xs[-1]==0
 if not any(x<0 for x in xs[:-1]):bad.append(xs[:-1])
 count+=1
expected=json.loads(Path('/tmp/oec/pequalnp-pilot-121/not-elimination/andbudget-profile-phase.json').read_text());assert bad==expected['phase_failures'];missed=[r for k,r in enumerate(mapping['rows']) if bool(out>>k&1)!=(k<52)];assert missed==expected['missed_row_masks'];assert len(bad)==len(missed)==6 and out>>52==0
invalid=json.loads((base/'profile-native16-invalid63.json').read_text());assert invalid['exit_code']==20 and 's UNSATISFIABLE' in (base/'profile-native16-invalid63.sol').read_text()
report={'scope':'Independent native positive control and incomplete target-phase audit; future profile-only restricted construction, no target witness.','source_sha256':digest(base/'andcount_budget_profile2056.py'),'native_clauses_checked':1429862,'native_variables':meta['variables'],'decoded_gates':64,'complete_boundary_rows':756,'actual_internal_row_values_checked':16*756,'target_clauses':count,'target_phase_failures':len(bad),'target_missed_rows':missed,'target_memberships':M,'target_active_records':A,'target_unshared_cost':M-A-1,'target_sha256':digest(prefix.with_suffix('.cnf')),'positive_model_sha256':digest(base/'profile-native16-free464.sol'),'invalid_fixed64_at63':'external UNSAT, as expected from budget81>80','first_AND_anchor':False}
Path('/tmp/oec/pequalnp-pilot-121/andbudget-profile-final-independent-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
