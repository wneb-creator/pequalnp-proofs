import json
answers=[]
for n in [7,9]:
 edges=[(i,i+1) for i in range(n-1)]
 def target(x):return any(x>>a&1 and x>>b&1 for a,b in edges)
 maxima=[x for x in range(1<<n) if not target(x) and all(x>>i&1 or target(x|(1<<i)) for i in range(n))]
 assert all(sum(bool(x>>a&1 and x>>b&1) for a,b in edges)<=x.bit_count() for x in range(1<<n))
 answers.append(dict(n=n,edges=edges,maximal_false_count=len(maxima),maximal_false_masks=maxima,assignments_checked=1<<n))
print(json.dumps(answers,indent=2))
