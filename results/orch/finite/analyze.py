from pathlib import Path
import itertools, json
D={0,1,3,9}
reps=[(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
edges={(p,l) for p in range(13) for l in range(13) if (p-l)%13 in D}
def row(a,b,m,t,dual):
 if dual: a,b=b,a
 sign=-1 if dual else 1
 A={i for i in range(13) if (a>>((sign*(m*i+t))%13))&1}
 B={i for i in range(13) if (b>>((sign*(m*i+t))%13))&1}
 return tuple(sorted(A)),tuple(sorted(B))
rows={row(a,b,m,t,d) for a,b in reps for m in (1,3,9) for t in range(13) for d in (False,True)}
nonedges={(p,l) for p in range(13) for l in range(13)}-edges
covered={(p,l) for A,B in rows for p in A for l in B}
print('edge count',len(edges),'generic rows',len(rows),'all nonedges covered',covered==nonedges)
print('per orbit',[(z,len({row(*z,m,t,d) for m in (1,3,9) for t in range(13) for d in (False,True)})) for z in reps])
print('size distribution',{(a,b):sum(len(A)==a and len(B)==b for A,B in rows) for a,b in sorted({(len(A),len(B)) for A,B in rows})})
print('input mask max sizes',max(len(A) for A,B in rows),max(len(B) for A,B in rows))
minimal_safe=[]
for k in (2,3,4,5):
 safe=[]
 for term in itertools.combinations(range(26),k):
  if any(set(s).issubset(term) for s in minimal_safe): continue
  if not any(all(i in A if i<13 else i-13 in B for i in term) for A,B in rows): safe.append(term)
 minimal_safe.extend(safe)
 print('minimal safe term degree',k,'count',len(safe),'left-only',sum(all(i<13 for i in s) for s in safe),'right-only',sum(all(i>=13 for i in s) for s in safe))
Path(__file__).with_name('rows.json').write_text(json.dumps({'edges':sorted(edges),'rows':sorted(rows),'safe':minimal_safe}))
