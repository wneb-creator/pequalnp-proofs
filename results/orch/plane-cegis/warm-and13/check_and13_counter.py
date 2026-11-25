import hashlib,json
from pathlib import Path

source=Path('direct_cnf_warm_nonread_and13.py').read_text()
start=source.index('minimum_ands=13\n')
end=source.index('add(previous[minimum_ands])',start)+len('add(previous[minimum_ands])')
fragment=source[start:end]
results=[]
for name,flags in [('twelve_AND_one_OR',[0]*12+[1]),('thirteen_AND',[0]*13),('thirteen_AND_one_OR',[0]*13+[1]),('fourteen_AND',[0]*14)]:
 count=[len(flags)];clauses=[];preferred={i+1:bool(op) for i,op in enumerate(flags)}
 def fresh():count[0]+=1;return count[0]
 def neg(x):return not x if type(x)is bool else -x
 def add(*ls):
  if any(x is True for x in ls):return
  c=[x for x in ls if x is not False]
  assert all(type(x)is int and x for x in c);clauses.append(c)
 env={'preferred':preferred,'ops':list(range(1,len(flags)+1)),'size':len(flags),'warm':[[op,0,1] for op in flags],'fresh':fresh,'neg':neg,'add':add}
 exec(compile(fragment,'exact_and13_counter_fragment','exec'),env)
 assert set(preferred)==set(range(1,count[0]+1))
 bad=[i+1 for i,c in enumerate(clauses) if not any(preferred[abs(x)]==(x>0) for x in c)]
 assigned={i+1:bool(op) for i,op in enumerate(flags)};conflict=False
 while True:
  changed=False
  for clause in clauses:
   if any(abs(x) in assigned and assigned[abs(x)]==(x>0) for x in clause):continue
   unknown=[x for x in clause if abs(x) not in assigned]
   if not unknown:conflict=True;break
   if len(unknown)==1:
    x=unknown[0];assigned[abs(x)]=x>0;changed=True
  if conflict or not changed:break
 expected=flags.count(0)>=13
 assert conflict==(not expected) and (not bad)==expected
 if expected:assert assigned==preferred
 r={'name':name,'AND_flags':flags.count(0),'OR_flags':flags.count(1),'variables':count[0],'clauses':len(clauses),'phase_unsatisfied_clauses':bad,'unit_propagation_conflict':conflict,'accepted':expected}
 Path('and13-counter-'+name+'.json').write_text(json.dumps({'result':r,'op_flags':flags,'clauses':clauses,'phase':preferred},indent=2)+'\n')
 results.append(r)
summary={'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'exact_counter_fragment_sha256':hashlib.sha256(fragment.encode()).hexdigest(),'results':results}
Path('and13-counter-threshold-check.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
