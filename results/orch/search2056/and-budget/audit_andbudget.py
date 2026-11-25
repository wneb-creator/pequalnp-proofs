import ast,datetime,hashlib,importlib.util,itertools,json,random,textwrap
from pathlib import Path
src=Path('/tmp/oec/pequalnp-pilot-121/andcount2056/andcount_budget2056.py')
sp=importlib.util.spec_from_file_location('reviewed_budget',src);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
text=src.read_text();block=textwrap.dedent(text[text.index('    def negate(value):'):text.index('    flipped =')]);compile(block,'counter-extract','exec')
counter_cases=0
for n in range(1,8):
 for threshold in range(n+1):
  for pattern in itertools.product((False,True),repeat=n):
   for parity in range(2):
    preferred={i+1:v for i,v in enumerate(pattern)};clauses=[]
    def fresh(v):
     i=len(preferred)+1;preferred[i]=bool(v);return i
    def add(*xs):
     assert all(type(x)is int and x for x in xs);clauses.append(list(xs))
    lits=[(i+1) if (i+parity)%2 else -(i+1) for i in range(n)]
    ns={'preferred':preferred,'fresh':fresh,'add':add,'budget_literals':lits,'threshold':threshold}
    exec(block,ns)
    satisfied=all(any(preferred[abs(x)]==(x>0) for x in c) for c in clauses)
    expected=sum(pattern[i]==(lits[i]>0) for i in range(n))<=threshold
    assert satisfied==expected
    counter_cases+=1
for a,b,c,z in itertools.product((False,True),repeat=4):
 clauses=[not a or z,not b or not c or z,not z or a or b,not z or a or c]
 assert all(clauses)==(z==(a or (b and c)))
rng=random.Random(20561800);edges,rows=m.geometry();materializer_cases=0;active_cases=0;false_cases=0;shared_cases=0
for trial in range(600):
 K=1+trial%20;records=[]
 for j in range(K):
  if rng.randrange(5)==0:records.append({'left':[],'right':[]});continue
  sides={}
  for key in ('left','right'):
   chosen=sorted(rng.sample(range(26+j),rng.randint(1,min(8,26+j))))
   if j and rng.randrange(5)==0:chosen=records[rng.randrange(j)][key] or chosen
   sides[key]=chosen
  records.append(sides)
 model={'ands':records,'output':sorted(rng.sample(range(K),rng.randint(1,K)))}
 ordinary=m.materialize(model);_,value=m.evaluate(model,rows);assert m.ordinary_eval(ordinary,rows)==value
 A=sum(bool(r['left']) for r in records);M=sum(len(r['left'])+len(r['right']) for r in records)+len(model['output'])
 assert ordinary['size']<=M-A-1
 assert sum(g[0]==0 for g in ordinary['gates'])<=A
 for row in rng.sample(rows,8):
  vals=[bool(row>>i&1) for i in range(26)]
  for r in records:vals.append(any(vals[i] for i in r['left']) and any(vals[i] for i in r['right']))
  wanted=any(vals[26+i] for i in model['output'])
  actual=[bool(row>>i&1) for i in range(26)]
  for op,a,b in ordinary['gates']:
   assert 0<=a<len(actual) and 0<=b<len(actual)
   actual.append((actual[a] or actual[b]) if op else (actual[a] and actual[b]))
  got=False if ordinary['constant_false'] else actual[ordinary['output']]
  assert got==wanted
 materializer_cases+=1;active_cases+=int(A<K);false_cases+=int(ordinary['constant_false']);shared_cases+=int(ordinary['size']<M-A-1)
star=m.star_model(14,edges);A=13;M=sum(len(r['left'])+len(r['right']) for r in star['ands'])+len(star['output']);assert M==78 and M+14-A==79 and m.materialize(star)['size']==64
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'static_verdict':'APPROVED; native SAT controls pending','counter_assignment_cases':counter_cases,'dp_cell_truth_cases':16,'materializer_random_models':materializer_cases,'inactive_models':active_cases,'constant_false_models':false_cases,'strict_size_reduction_models':shared_cases,'rows_per_model':756,'independent_boolean_rows_per_model':8,'fixed_star_K':14,'fixed_star_memberships':M,'fixed_star_active':A,'fixed_star_budget_lhs':79,'star_limit64_satisfies':True,'star_limit63_violates_by':1,'cost_proof':'For a active records with both operand subsets nonempty and nonempty output, explicit duplicated OR expansion costs M-a-1. Counter M+(K-a)<=limit+1+K implies cost<=limit. False propagation, idempotence, exact-OR caching and dead-gate pruning can only reduce ordinary size. Primary inputs need not be selected directly at output because no singleton assignment is true in the target; the model remains explicitly a restricted synthesis search.'}
Path('/tmp/oec/pequalnp-pilot-121/not-elimination/andbudget-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
