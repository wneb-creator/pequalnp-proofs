from pathlib import Path
import json,itertools,collections
base=Path('/tmp/oec/pequalnp-pilot-78/finitefield')
ijs=[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]
index={pair:i for i,pair in enumerate(ijs)}
terms=[[index[tuple(sorted((i,j)))] for i,j in enumerate(s)] for s in itertools.permutations(range(4))]
mons=[(i,j) for d in range(4) for i in range(d+1) for j in [d-i]]
mons4=[(i,j) for d in range(1,5) for i in range(d+1) for j in [d-i]]
def rank(rows,p):
 a=[[x%p for x in r] for r in rows];k=0
 for j in range(len(a[0])):
  i=next((i for i in range(k,len(a)) if a[i][j]),None)
  if i is None:continue
  a[k],a[i]=a[i],a[k];u=pow(a[k][j],-1,p);a[k]=[v*u%p for v in a[k]]
  for i in range(len(a)):
   if i!=k:
    u=a[i][j];a[i]=[(x-u*y)%p for x,y in zip(a[i],a[k])]
  k+=1
  if k==len(a):break
 return k

def gradients(A,B,p):
 G=[collections.defaultdict(int) for _ in range(10)]
 for t in terms:
  for r in range(4):
   f={(0,0):1}
   for k in range(4):
    if k==r:continue
    a,b=A[t[k]],B[t[k]];h=collections.defaultdict(int)
    for (i,j),v in f.items():
     h[i,j]+=v;h[i+1,j]+=v*a;h[i,j+1]+=v*b
    f={m:v%p for m,v in h.items() if v%p}
   for m,v in f.items():G[t[r]][m]=(G[t[r]][m]+v)%p
 return G
for p in [5,7,11,13]:
 planes=json.loads((base/f'f{p}-t00-zero-planes.json').read_text());out=[];counts=collections.Counter()
 for A,B in planes:
  G=gradients(A,B,p)
  mat=[[g[m] for g in G] for m in mons]
  ext=10-rank(mat,p)
  ext00=10-rank(mat+[[1]+[0]*9],p)
  dm=[]
  for i,j in mons4:
   dm.append([g[i-1,j] if i else 0 for g in G]+[g[i,j-1] if j else 0 for g in G])
  dm+=[[1]+[0]*19,[0]*10+[1]+[0]*9]
  deformation=20-rank(dm,p)-4
  rd=rank([[r[i] for i in [0,4,7,9]] for r in [A,B]],p)
  row={'basis':[A,B],'diag_rank':rd,'extension_dimension':ext,'extension_t00_dimension':ext00,'slice_fano_tangent_dimension':deformation}
  out.append(row);counts[rd,ext,ext00,deformation]+=1
 print('F',p,'count by (diag rank, extension dimension, extension T00 dimension, slice Fano tangent dimension):')
 for key,n in sorted(counts.items()):print(key,n)
 if p==13:
  for r in out:
   if r['diag_rank']:print('F13 nonhollow',json.dumps(r))
 (base/f'f{p}-slice-tangents.json').write_text(json.dumps(out,indent=2))
