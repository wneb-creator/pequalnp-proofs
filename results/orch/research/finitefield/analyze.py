import sys, json, collections, itertools
from pathlib import Path
p=int(sys.argv[1]); base=Path(sys.argv[2])
dirs=[tuple(map(int,s.split())) for s in Path(str(base)+'-directions.txt').read_text().splitlines()]
edges=[tuple(map(int,s.split())) for s in Path(str(base)+'-edges.txt').read_text().splitlines()]
def rref(rows):
 a=[list(r) for r in rows]; r=0
 for c in range(len(a[0])):
  k=next((i for i in range(r,len(a)) if a[i][c]),None)
  if k is None: continue
  a[r],a[k]=a[k],a[r]
  d=pow(a[r][c],-1,p); a[r]=[x*d%p for x in a[r]]
  for i in range(len(a)):
   if i!=r:
    d=a[i][c];a[i]=[(x-d*y)%p for x,y in zip(a[i],a[r])]
  r+=1
  if r==len(a):break
 return tuple(tuple(row) for row in a[:r])
lines={rref([dirs[i],dirs[j]]) for i,j in edges}
diag=[0,4,7,9]
byrank=collections.defaultdict(list)
for line in lines:
 rank=len(rref([[v[i] for i in diag] for v in line])); byrank[rank].append(line)
print('P',p,'2planes',len(lines),'diagonal_rank_counts',{r:len(xs) for r,xs in byrank.items()})
for r,xs in sorted(byrank.items()):
 print('diagonal_rank',r,'examples',json.dumps(sorted(xs)[:8]))
Path(str(base)+'-2planes.json').write_text(json.dumps(sorted(lines)))
# Independent reference check of tangent, all homogeneous coefficients and sampled pair spans.
perms=list(itertools.permutations(range(4)))
ijs=[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]
def coeff(v):
 m=[[0]*4 for _ in range(4)]
 for (i,j),x in zip(ijs,v):m[i][j]=m[j][i]=x
 out=[0]*5
 for s in perms:
  poly=[1]
  for i in range(4):
   nxt=[0]*(len(poly)+1)
   for k,x in enumerate(poly):nxt[k]=(nxt[k]+x)%p;nxt[k+1]=(nxt[k+1]+x*m[i][s[i]])%p
   poly=nxt
  out=[(x+y)%p for x,y in zip(out,poly)]
 return out
for v in dirs[::max(1,len(dirs)//100)]: assert coeff(v)==[24%p,0,0,0,0]
for a,b in list(sorted(lines))[:100]:
 for k in range(p):
  v=[(x+k*y)%p for x,y in zip(a,b)];assert coeff(v)==[24%p,0,0,0,0]
print('independent reference checks passed')
