from pathlib import Path
import sys,json,itertools
n,s=int(sys.argv[1]),int(sys.argv[2]);edges=json.loads(Path(sys.argv[3]).read_text());out=Path(sys.argv[4]);mode=sys.argv[5];safe=mode=='safe'
R=1<<n;A=R+n+s+2
truth=lambda r:any((r>>a&1) and (r>>b&1) for a,b in edges)
true_rows=[r for r in range(R) if truth(r)];false_rows=[r for r in range(R) if not truth(r)]
mint=[r for r in true_rows if not any(q!=r and q&r==q for q in true_rows)]
maxf=[r for r in false_rows if not any(q!=r and q&r==r for q in false_rows)]
rows=sorted(mint+maxf)
ix=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
F=[]
def onehot(vs):
 F.append(vs)
 F.extend([-a,-b] for a,b in itertools.combinations(vs,2))
for j in range(s):
 onehot([ix(0,j,d) for d in range(3)])
 for side in (1,2):onehot([ix(side,j,k) for k in range(n+j+1)])
 for a in range(n+j+1):
  for b in range(a):F.append([-ix(1,j,a),-ix(2,j,b)])
 for r in rows:
  for side in (1,2):
   u=ix(side+3,j,r)
   for k in range(n+j+1):
    sel=ix(side,j,k)
    if k<n:F.append([-sel,u if r>>k&1 else -u])
    elif k<n+j:
     v=ix(3,k-n,r);F.extend([[-sel,-u,v],[-sel,u,-v]])
    else:F.append([-sel,-u])
  w,u,v=ix(3,j,r),ix(4,j,r),ix(5,j,r);a,b,c=[ix(0,j,d) for d in range(3)]
  F.extend([[-a,-w,u],[-a,-w,v],[-a,w,-u,-v],[-b,w,-u],[-b,w,-v],[-b,-w,u,v],[-c,w]])
  if safe and not truth(r):F.append([-a,-w])
 if safe:F.append([-ix(0,j,2)])
for j in range(s-1):
 F.append([ix(side,k,n+j) for k in range(j+1,s) for side in (1,2)])
for r in rows:F.append([ix(3,s-1,r) if truth(r) else -ix(3,s-1,r)])
nv=6*(s+1)*A
if mode=='unsafe':
 markers=[]
 for j in range(s):
  for r in maxf:
   nv+=1;markers.append(nv)
   F.extend([[-nv,ix(0,j,0),ix(0,j,2)],[-nv,ix(3,j,r)]])
 F.append(markers)
with out.open('w') as f:
 f.write(f'p cnf {nv} {len(F)}\n')
 for clause in F:f.write(' '.join(map(str,clause))+' 0\n')
print(json.dumps({'n':n,'gates':s,'mode':mode,'rows':rows,'minimal_true':mint,'maximal_false':maxf,'variables':nv,'clauses':len(F)}))
