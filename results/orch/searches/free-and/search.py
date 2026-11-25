import argparse,json,random,time
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('--n',type=int,default=6)
p.add_argument('--ors',type=int,default=4)
p.add_argument('--seconds',type=float,default=40)
p.add_argument('--seed',type=int,default=71)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
r=random.Random(a.seed)
n=a.n
full=(1<<(1<<n))-1
inputs=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
edges=[(i,(i+1)%n) for i in range(n)]
target=0
pairmask=0
for u,v in edges:
 target|=inputs[u]&inputs[v]
 pairmask|=1<<((1<<u)|(1<<v))
base={}
for mask in range(1,1<<n):
 f=full
 for i in range(n):
  if mask>>i&1:f&=inputs[i]
 if f not in base or mask.bit_count()<base[f].bit_count():base[f]=mask

def value(mask,gs):
 out=full
 while mask:
  bit=mask&-mask
  out&=gs[bit.bit_length()-1]
  mask-=bit
 return out

def evaluate(prog):
 gs=inputs.copy()
 pool=base.copy()
 for i,(m1,m2) in enumerate(prog):
  g=value(m1,gs)|value(m2,gs)
  gs.append(g)
  mask=1<<(n+i)
  new={g:mask}
  for f,expr in pool.items():
   h=f&g
   hm=expr|mask
   if h not in pool and (h not in new or hm.bit_count()<new[h].bit_count()):new[h]=hm
  for f,expr in new.items():
   if f not in pool or expr.bit_count()<pool[f].bit_count():pool[f]=expr
 best=-100000
 valid=0
 chosen=None
 for f,expr in pool.items():
  cov=(f&pairmask).bit_count()
  bad=(f&~target).bit_count()
  miss=(target&~f).bit_count()
  score=100*cov-45*bad-miss
  if score>best:best=score;chosen=(f,expr,cov,bad,miss)
  if not bad and cov>valid:valid=cov
  if not bad and cov>a.ors+1:
   return best,valid,{'program':prog,'output_mask':expr,'truth':f,'edges':edges,'n':n,'ors':a.ors,'accepted_edges':cov},len(pool)
 return best,valid,None,len(pool)

def randmask(k):
 count=r.choices([1,2,3,4],[58,30,10,2])[0]
 return sum(1<<j for j in r.sample(range(k),min(k,count)))

def fresh():return [(randmask(n+i),randmask(n+i)) for i in range(a.ors)]
start=time.time()
count=0
best=-100000
best_valid=0
best_prog=None
largest_pool=0
found=None
while time.time()-start<a.seconds:
 prog=fresh()
 score,valid,witness,poolsize=evaluate(prog)
 for step in range(300):
  count+=1
  largest_pool=max(largest_pool,poolsize)
  if valid>best_valid:best_valid=valid;print('valid_edges',valid,'evaluations',count,flush=True)
  if score>best:best=score;best_prog=list(prog)
  if witness:found=witness;break
  cand=list(prog)
  i=r.randrange(a.ors)
  m1,m2=cand[i]
  if r.random()<0.5:m1=randmask(n+i)
  else:m2=randmask(n+i)
  cand[i]=(m1,m2)
  newscore,newvalid,witness,poolsize=evaluate(cand)
  temp=max(4,70*(1-step/300))
  import math
  if newscore>=score or r.random()<math.exp((newscore-score)/temp):
   prog,score,valid=cand,newscore,newvalid
  elif witness:
   prog=cand
  if time.time()-start>=a.seconds:break
 if found:break
result={'elapsed':time.time()-start,'evaluations':count,'best_score':best,'best_valid_edges':best_valid,'largest_meet_closure':largest_pool,'best_program':best_prog,'witness':found,'seed':a.seed,'n':n,'ors':a.ors}
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2),flush=True)
