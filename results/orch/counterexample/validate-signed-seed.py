from pathlib import Path
import json
n,s=10,18;R=1<<n;A=R+n+s+2
p=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
raw=[list(map(int,line.split())) for line in Path('signed18-seed.txt').read_text().splitlines()[1:]]
pending={j:(op,a,b) for j,op,a,b in raw};ren={i:i for i in range(n)};c=[]
while pending:
 ready=[]
 for old,(op,a,b) in pending.items():
  if a in ren and b in ren:
   a,b=ren[a],ren[b]
   if a>b:a,b=b,a
   ready.append(((a,b,op),old,op,a,b))
 _,old,op,a,b=min(ready);ren[old]=n+len(c);c.append([op,a,b]);del pending[old]
assert len(c)==s and ren[n+s-1]==n+s-1 and c[0]==[1,0,2]
Path('signed18-seed.txt').write_text('errors 4\n'+'\n'.join(f'{n+j} {op} {a} {b}' for j,(op,a,b) in enumerate(c))+'\n')
truth=set()
for j,(op,a,b) in enumerate(c):truth.update([p(0,j,op),p(1,j,a),p(2,j,b)])
for r in range(R):
 w=[bool(r>>i&1) for i in range(n)]
 for j,(op,a,b) in enumerate(c):
  av=w[a];bv=w[b]
  z=av and bv if op==0 else av or bv if op==1 else av and not bv if op==2 else not av and bv
  w.append(z)
  for kd,val in [(3,z),(4,av),(5,bv)]:
   if val:truth.add(p(kd,j,r))
oldvars=10*(s+1)*A;nv=oldvars+s+n+s
for i in range(n+2*s):
 for k in range(1,min(i+1,20)+1):
  nv+=1
  if k<=min(i+1,s):truth.add(nv)
failures=[];count=0
with Path('signed18-cost19.cnf').open() as f:
 head=f.readline().split()
 for count,line in enumerate(f,1):
  lits=list(map(int,line.split()))[:-1]
  if not any((v in truth) if v>0 else (-v not in truth) for v in lits):failures.append([count,lits])
report={'variables':int(head[2]),'declared_clauses':int(head[3]),'read_clauses':count,'failures':failures}
assert count==int(head[3]) and int(head[2])==nv
Path('signed-seed-validation.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report))
