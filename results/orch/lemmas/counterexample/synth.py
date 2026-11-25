from pathlib import Path
from itertools import combinations
import json,subprocess,time,sys,shutil
BASE=Path('/tmp/oec/pequalnp-pilot-134')
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x): return any((x>>a&1) and (x>>b&1) for a,b in EDGES)
class CNF:
 def __init__(self): self.n=0;self.cs=[]
 def var(self): self.n+=1;return self.n
 def add(self,*c): self.cs.append(c)
 def one(self,a):
  self.add(*a)
  for x,y in combinations(a,2):self.add(-x,-y)
 def write(self,p):
  with p.open('w') as f:
   f.write(f'p cnf {self.n} {len(self.cs)}\n')
   for c in self.cs:f.write(' '.join(map(str,c))+' 0\n')
def build(rows,n,normal=False,seednot=False,bounded3=False,rawraw=False,constantCuts=False,redCuts=False):
 f=CNF(); ops=[];left=[];right=[]
 for i in range(n):
  ops.append([f.var() for _ in range(4 if bounded3 else 3)]);f.one(ops[-1]);left.append([f.var() for _ in range(12+i)]);right.append([f.var() for _ in range(12+i)])
  f.one(left[-1]);f.one(right[-1]);f.add(-ops[-1][2],right[-1][0])
  if bounded3:
   f.add(-ops[-1][3],left[-1][0]);f.add(-ops[-1][3],right[-1][0])
  for a in range(12+i):
   for b in range(a):f.add(ops[-1][2],-left[-1][a],-right[-1][b])
 for j in range(10):f.add(*(left[i][j] for i in range(n)),*(right[i][j] for i in range(n)))
 for i in range(n-1):f.add(*(left[j][12+i] for j in range(i+1,n)),*(right[j][12+i] for j in range(i+1,n)))
 if seednot:
  f.one([op[2] for op in ops])
  for i in range(n):f.add(-ops[i][2],left[i][10])
 if bounded3:
  for ns in combinations([op[2] for op in ops],4):f.add(*(-v for v in ns))
 if redCuts:
  seedReaders=[left[i][10] for i in range(n)]+[right[i][10] for i in range(n)]
  for ns in combinations([op[2] for op in ops],3):f.add(*(-v for v in ns),*seedReaders)
 if rawraw:
  for i in range(n):
   for u,v in combinations(range(10),2):
    for vertex in [u,v]:
     if vertex in [0,2]:continue
     other=[left[j][vertex] for j in range(n) if j!=i]+[right[j][vertex] for j in range(n) if j!=i]
     f.add(ops[i][2],ops[i][3],-left[i][u],-right[i][v],*other)
 if normal:
  for i in range(n):
   f.add(-ops[i][2],-left[i][11])
   for j in range(12+i):f.add(ops[i][2],-left[i][j],-right[i][j])
   for j in range(i):f.add(-ops[i][2],-left[i][12+j],-ops[j][2])
  for i in range(n-1):
   dep=[left[i+1][12+i],right[i+1][12+i]]
   for a in range(12+i):
    for b in range(a):f.add(-left[i][a],-left[i+1][b],*dep)
    for c in range(12+i):
     for d in range(c):f.add(-left[i][a],-left[i+1][a],-right[i][c],-right[i+1][d],*dep)
 rowYs={}
 for x in rows:
  ys=[]
  for i in range(n):
   a,b,y=f.var(),f.var(),f.var();ys.append(y)
   for ss,v in [(left[i],a),(right[i],b)]:
    for j,s in enumerate(ss):
     if j<12:
      val=((x>>j&1) if j<10 else ((x&5)==5) if j==10 else False)
      f.add(-s,v if val else -v)
     else:
      prev=ys[j-12];f.add(-s,-v,prev);f.add(-s,v,-prev)
   ao,oo,no=ops[i][:3]
   f.add(-ao,-a,-b,y);f.add(-ao,a,-y);f.add(-ao,b,-y)
   f.add(-oo,a,b,-y);f.add(-oo,-a,y);f.add(-oo,-b,y)
   f.add(-no,a,y);f.add(-no,-a,-y)
   if bounded3:f.add(-ops[i][3],y)
  f.add(ys[-1] if target(x) else -ys[-1])
  rowYs[x]=ys
 if constantCuts:
  assert n==18
  for endpoint in [0,2]:
   restricted=[x for x in rowYs if not (x>>endpoint&1)]
   assert len(restricted)==512
   constants=[]
   zeroFlags=[];oneFlags=[]
   for i in range(n):
    zero,one=f.var(),f.var();constants.extend([zero,one])
    zeroFlags.append(zero);oneFlags.append(one)
    column=[rowYs[x][i] for x in restricted]
    f.add(zero,*column);f.add(one,*(-v for v in column))
    for v in column:f.add(-zero,-v);f.add(-one,v)
   for triple in combinations(constants,3):f.add(*(-v for v in triple))
   if redCuts:
    red=[f.var() for _ in range(n)]
    for i in range(n):
     f.add(-zeroFlags[i],red[i]);f.add(-oneFlags[i],red[i])
     incoming=[]
     for selectors in [left[i],right[i]]:
      c0,c1=f.var(),f.var();incoming.append((c0,c1))
      for j,sel in enumerate(selectors):
       if j<12:
        iszero=j in [endpoint,10,11]
        f.add(-sel,c0 if iszero else -c0);f.add(-sel,-c1)
       else:
        for c,t in [(c0,zeroFlags[j-12]),(c1,oneFlags[j-12])]:
         f.add(-sel,-c,t);f.add(-sel,c,-t)
     for c0,c1 in incoming:
      for op in [ops[i][0],ops[i][1]]:
       f.add(-op,-c0,red[i]);f.add(-op,-c1,red[i])
     f.add(-ops[i][2],-incoming[0][0],red[i]);f.add(-ops[i][2],-incoming[0][1],red[i])
     for j in range(12+i):
      f.add(-ops[i][0],-left[i][j],-right[i][j],red[i])
      f.add(-ops[i][1],-left[i][j],-right[i][j],red[i])
     for j in range(i):f.add(-ops[i][2],-ops[j][2],-left[i][12+j],red[i])
    for triple in combinations(red,3):f.add(*(-v for v in triple))
 return f,ops,left,right
def decode(out,ops,left,right):
 model=set()
 for l in out.splitlines():
  if l.startswith('v '):model.update(int(v) for v in l.split()[1:] if int(v)>0)
 return [(next(k for k,v in enumerate(os) if v in model),next(k for k,v in enumerate(ls) if v in model),next(k for k,v in enumerate(rs) if v in model)) for os,ls,rs in zip(ops,left,right)]
def evaluate(gs,x):
 vals=[bool(x>>j&1) for j in range(10)]+[(x&5)==5,False]
 for op,a,b in gs:vals.append((vals[a] and vals[b]) if op==0 else (vals[a] or vals[b]) if op==1 else not vals[a] if op==2 else True)
 return vals[-1]
def main():
 n=int(sys.argv[1]) if len(sys.argv)>1 else 18
 seconds=int(sys.argv[2]) if len(sys.argv)>2 else 120
 mode=sys.argv[3] if len(sys.argv)>3 else ''
 normal=mode in ['normal','seednot']
 seednot=mode=='seednot'
 bounded3=mode in ['bounded3','bounded3raw','bounded3rawconst','bounded3rawred']
 rawraw=mode in ['bounded3raw','bounded3rawconst','bounded3rawred']
 constantCuts=mode in ['bounded3rawconst','bounded3rawred']
 redCuts=mode=='bounded3rawred'
 proofCap=int(sys.argv[4]) if len(sys.argv)>4 else 280_000_000
 label=f'{n}-{mode}' if mode else str(n)
 rows=set(range(1024)) if bounded3 else set(x for x in range(1024) if x.bit_count()<=2 or not target(x))
 print('initial rows',len(rows),flush=True)
 for it in range(20):
  f,ops,left,right=build(sorted(rows),n,normal,seednot,bounded3,rawraw,constantCuts,redCuts);cnf=BASE/f'synth-{label}-{it}.cnf';f.write(cnf)
  output=BASE/f'synth-{label}-{it}.out';print('solve',it,'vars',f.n,'clauses',len(f.cs),flush=True)
  f.cs.clear()
  with output.open('w') as log:
   args=[str(BASE/'kissat/build/kissat'),f'--time={seconds}',str(cnf)]
   if bounded3:args.append(str(BASE/f'synth-{label}-{it}.drat'))
   if bounded3:
    child=subprocess.Popen(args,stdout=log,stderr=subprocess.STDOUT)
    proof=BASE/f'synth-{label}-{it}.drat'
    while child.poll() is None:
     if (proof.exists() and proof.stat().st_size>proofCap) or shutil.disk_usage(BASE).free<64_000_000:
      print('proof or free-disk cap reached; terminating solver without verdict',flush=True)
      child.terminate();break
     time.sleep(2)
    child.wait();p=child
   else:p=subprocess.run(args,stdout=log,stderr=subprocess.STDOUT)
  out=output.read_text();print('solver return',p.returncode,flush=True)
  if p.returncode!=10: return
  gs=decode(out,ops,left,right);bad=[x for x in range(1024) if evaluate(gs,x)!=target(x)]
  print('model',gs,'wrong',len(bad),flush=True)
  (BASE/f'synth-{label}-{it}-model.json').write_text(json.dumps({'gates':gs,'bad':bad})+'\n')
  if not bad: print('FOUND',flush=True); return
  rows.update(bad)
if __name__=='__main__':main()
