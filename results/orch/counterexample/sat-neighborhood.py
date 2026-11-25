from pathlib import Path
import subprocess,time,json,sys
n,s=10,19
A=2**n+n+s+2
p=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
solver='/tmp/oec/pequalnp-pilot-100/sat/cadical/build/cadical'
base=Path('base-all.cnf').read_text().splitlines(keepends=True)
_,_,vs,cs=base[0].split();vs,cs=int(vs),int(cs)
basebody=''.join(base[1:]);del base
candidate=[list(map(int,x.split())) for x in Path('best-circuit.txt').read_text().splitlines()[1:]]
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def check_model(k):
 text=Path(f'sat-local-{k}.stdout.txt').read_text()
 model=set()
 for line in text.splitlines():
  if line.startswith('v '):model.update(int(x) for x in line[2:].split() if int(x)>0)
 gates=[]
 for j in range(s):
  op=next(q for q in range(4) if p(0,j,q) in model)
  a=next(q for q in range(n+j+1) if p(1,j,q) in model)
  b=next(q for q in range(n+j+1) if p(2,j,q) in model)
  gates.append((op,a,b))
 out=next(q for q in range(n+s+1) if p(6,0,q) in model)
 errors=[]
 for x in range(1024):
  w=[bool(x>>i&1) for i in range(n)]
  for op,a,b in gates:
   av=w[a] if a<len(w) else False;bv=w[b] if b<len(w) else False
   w.append(av and bv if op==0 else av or bv if op==1 else True if op==2 else not av)
  got=w[out] if out<len(w) else False
  want=any((x>>a)&1 and (x>>b)&1 for a,b in edges)
  if got!=want:errors.append(x)
 data=dict(gates=gates,output=out,errors=errors)
 Path(f'sat-witness-{k}.json').write_text(json.dumps(data,indent=2))
 print('WITNESS',json.dumps(data),flush=True)
 return not errors
for k in range(1,8):
 extra=[]
 def add(*c):extra.append(c)
 nv=vs
 changes=[]
 for j,(_,op,a,b) in enumerate(candidate):
  nv+=1;changes.append(nv)
  if op==2:op=3;b=a
  elif a>b:a,b=b,a
  for v in [p(0,j,op),p(1,j,a),p(2,j,b)]:add(nv,v)
 add(*[p(0,j,3) for j in range(s)])
 add(p(6,0,n+s-1))
 last={}
 for i,b in enumerate(changes):
  curr={}
  for j in range(1,min(i+1,k+1)+1):nv+=1;curr[j]=nv
  add(-b,curr[1])
  for j,v in last.items():
   if j in curr:add(-v,curr[j])
   if j+1 in curr:add(-v,-b,curr[j+1])
  last=curr
 add(-last[k+1])
 path=Path('local-current.cnf')
 with path.open('w') as f:
  f.write(f'p cnf {nv} {cs+len(extra)}\n');f.write(basebody)
  for c in extra:f.write(' '.join(map(str,c))+' 0\n')
 start=time.time()
 with Path(f'sat-local-{k}.stdout.txt').open('w') as out,Path(f'sat-local-{k}.stderr.txt').open('w') as err:
  r=subprocess.run([solver,'-q','-t','45',str(path)],stdout=out,stderr=err)
 print('k',k,'code',r.returncode,'seconds',round(time.time()-start,2),flush=True)
 if r.returncode==10:
  check_model(k)
  break
