import sys,json,itertools
from pathlib import Path
n,s=int(sys.argv[1]),int(sys.argv[2]);edges=[tuple(map(int,e)) for e in sys.argv[3].split(',')];out=Path(sys.argv[4])
R=1<<n;A=R+n+s+2
ix=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
fun=lambda r:any((r>>a&1) and (r>>b&1) for a,b in edges)
neg=[r for r in range(R) if not fun(r)];maxfalse=[r for r in neg if not any(q!=r and q&r==r for q in neg)]
rows=sorted(set([r for r in range(R) if r.bit_count()<=2]+maxfalse+[R-1]))
if len(sys.argv)>5: rows=sorted(set(rows+json.loads(Path(sys.argv[5]).read_text())))
F=[];ops=[1,2,4,8,14,13,11,7]
for j in range(s):
 os=[ix(0,j,a) for a in range(8)];F.append(os)
 for a,b in itertools.combinations(os,2):F.append([-a,-b])
 for sd in [1,2]:
  src=[ix(sd,j,k) for k in range(n+j)];F.append(src)
  for a,b in itertools.combinations(src,2):F.append([-a,-b])
 for a in range(n+j):
  for b in range(a+1):F.append([-ix(1,j,a),-ix(2,j,b)])
 for sd in [1,2]:
  for r in rows:
   u=ix(sd+3,j,r)
   for k in range(n+j):
    src=ix(sd,j,k)
    if k<n:F.append([-src,u if r>>k&1 else -u])
    else:
     w=ix(3,k-n,r);F.extend([[-src,-u,w],[-src,u,-w]])
 for r in rows:
  u,v,w=ix(4,j,r),ix(5,j,r),ix(3,j,r)
  for op,mask in enumerate(ops):
   sel=ix(0,j,op)
   for a,b in itertools.product(range(2),repeat=2):
    val=bool(mask>>(2*a+b)&1);F.append([-sel,-u if a else u,-v if b else v,w if val else -w])
for j in range(s-1):F.append([ix(sd,k,n+j) for sd in [1,2] for k in range(j+1,s)])
for r in rows:F.append([ix(3,s-1,r) if fun(r) else -ix(3,s-1,r)])
# Topological adjacent swaps: increasing first source, then second source if independent.
for j in range(s-1):
 base=[ix(1,j+1,n+j),ix(2,j+1,n+j)]
 for a in range(n+j):
  for b in range(a):F.append(base+[-ix(1,j,a),-ix(1,j+1,b)])
  for c in range(a+1,n+j):
   for d in range(a+1,c):F.append(base+[-ix(1,j,a),-ix(1,j+1,a),-ix(2,j,c),-ix(2,j+1,d)])
out.write_text(f'p cnf {6*(s+1)*A} {len(F)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in F))
out.with_suffix('.meta.json').write_text(json.dumps({'n':n,'s':s,'edges':edges,'rows':rows,'ops':ops,'A':A})+'\n')
print('rows',len(rows),'variables',6*(s+1)*A,'clauses',len(F))
