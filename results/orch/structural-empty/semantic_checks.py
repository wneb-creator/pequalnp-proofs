from pathlib import Path
import json
out=Path('/tmp/oec/pequalnp-pilot-87/counterexample/structural-empty')
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def indep(s):return not any((s>>a&1)and(s>>b&1)for a,b in edges)
nb=[{b for a,b in edges if a==i}|{a for a,b in edges if b==i}for i in range(10)]
exceptions={}
for i in range(10):
 xs=[s for s in range(1024)if indep(s)and not(s>>i&1)and all(not indep(s|1<<z)for z in nb[i])]
 assert len(xs)==2 and all(s.bit_count()==3 for s in xs)
 assert all(indep(s|1<<i)and(s|1<<i).bit_count()==4 for s in xs)
 exceptions[i]=[[v for v in range(10)if s>>v&1]for s in xs]
assert exceptions[0]==[[3,6,7],[2,8,9]]
print('PASS exact independent blockers per vertex:',json.dumps(exceptions,sort_keys=True))
f=['and',['or',0,['or',1,2]],['or',3,['and',['or',0,4],['or',1,5]]]]
q=['or',['and',3,['or',0,['or',1,2]]],['or',['and',0,['or',1,5]],['and',1,4]]]
def leaves(e):return 1 if isinstance(e,int)else leaves(e[1])+leaves(e[2])
def value(e,x):
 if isinstance(e,int):return bool(x>>e&1)
 a=value(e[1],x);b=value(e[2],x);return a and b if e[0]=='and'else a or b
pairs=[(a,b)for a in range(6)for b in range(a+1,6)if value(f,(1<<a)|(1<<b))]
assert pairs==[(0,1),(0,3),(0,5),(1,3),(1,4),(2,3)]
assert all(value(q,x)==any(x>>a&1 and x>>b&1 for a,b in pairs)for x in range(64))
assert leaves(f)==8 and leaves(q)==9
assert [x for x in range(64)if value(f,x)!=value(q,x)]==[52]
print('PASS extraction example:8leaf input,9leaf quadratic formula, only differing truth row52={2,4,5}; exhaustive DP excludes≤8leaf quadratic formula.')
out.joinpath('semantic-check-results.json').write_text(json.dumps({'blockers':exceptions,'extraction_input':f,'quadratic_formula':q,'quadratic_edges':pairs,'difference_rows':[52]},indent=2))
