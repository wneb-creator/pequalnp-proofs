import itertools,json
from pathlib import Path
D={0,1,3,9}; ALL=(1<<13)-1
reps=[(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
lines=[sum(1<<((w+d)%13) for d in D) for w in range(13)]
pencils=[sum(1<<w for w in range(13) if (p-w)%13 in D) for p in range(13)]
coltrip={sum(1<<i for i in t) for line in lines for t in itertools.combinations([i for i in range(13) if line>>i&1],3)}
conctrip={sum(1<<i for i in t) for pen in pencils for t in itertools.combinations([i for i in range(13) if pen>>i&1],3)}
def row(a,b,m,t,dual):
 if dual:a,b=b,a
 sign=-1 if dual else 1
 return tuple(sum(1<<i for i in range(13) if (mask>>((sign*(m*i+t))%13))&1) for mask in (a,b))
rows={row(a,b,m,t,d) for a,b in reps for m in (1,3,9) for t in range(13) for d in (False,True)}
def nonneighbors(A):return sum(1<<w for w in range(13) if not A&lines[w])
def facts(S):
 projected={(A&S,B) for A,B in rows}
 maximal=set()
 sub=S
 while True:
  B=nonneighbors(sub)
  cl=sum(1<<p for p in range(13) if S>>p&1 and not pencils[p]&B)
  if cl==sub:maximal.add((sub,B))
  if not sub:break
  sub=(sub-1)&S
 missing=maximal-projected
 return {'points':[i for i in range(13) if S>>i&1],'generic_projected_rows':len(projected),'induced_max_false_count':len(maximal),'missing_max_false':len(missing),'missing_sizes':sorted({(A.bit_count(),B.bit_count()) for A,B in missing}),'point_triples':sum(S&t==t for t in coltrip)}
rows7=[facts(sum(1<<i for i in S)) for S in itertools.combinations(range(13),7)]
summary={}
for r in rows7:
 key=(r['induced_max_false_count'],r['missing_max_false'],r['point_triples'])
 summary[key]=summary.get(key,0)+1
out={'all_seven_point_subsets':len(rows7),'distribution':[{**dict(zip(['max_false','missing','point_triples'],key)),'count':count} for key,count in sorted(summary.items())],'example0123456':facts(127),'min_missing_example':min(rows7,key=lambda r:r['missing_max_false']),'max_missing_example':max(rows7,key=lambda r:r['missing_max_false'])}
print(json.dumps(out,indent=2))
Path(__file__).with_name('projection-result.json').write_text(json.dumps(out,indent=2))
