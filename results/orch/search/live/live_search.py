import argparse, functools, itertools, json, time, importlib.util
from pathlib import Path
E=((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5))
N=10; FULL=(1<<1024)-1
INPUTS=tuple(sum(1<<r for r in range(1024)if r>>i&1)for i in range(N))
TARGET=0
for a,b in E:TARGET|=INPUTS[a]&INPUTS[b]
ADJ=[set()for _ in range(N)]
for a,b in E:ADJ[a].add(b);ADJ[b].add(a)

def autos():
 out=[]
 def visit(p,left):
  if not left:out.append(tuple(p));return
  j=len(p)
  for a in left:
   if all((k in ADJ[j])==(p[k] in ADJ[a])for k in range(j)):
    visit(p+[a],left-{a})
 visit([],set(range(N)));return out
AUTOS=autos()

def swaps_for(p):
 q=list(range(N));sw=[]
 for i in range(N):
  if q[i]!=p[i]:
   j=q.index(p[i]);q[i],q[j]=q[j],q[i];sw.append((i,j))
 return sw
SWAPS={p:swaps_for(p)for p in AUTOS}
MASKS={(i,j):INPUTS[i]&~INPUTS[j]&FULL for i in range(N)for j in range(i+1,N)}
@functools.lru_cache(300000)
def moved(v,p):
 for i,j in SWAPS[p]:
  delta=(1<<j)-(1<<i);mask=MASKS[i,j]
  t=((v>>delta)^v)&mask;v^=t^(t<<delta)
 return v

def check_moves():
 for p in AUTOS:
  assert moved(TARGET,p)==TARGET
  assert {moved(v,p)for v in INPUTS}==set(INPUTS)

def opval(op,a,b):
 if op==0:return a&b
 if op==1:return a|b
 if op==2:return a&~b&FULL
 return ~a&b&FULL

class Search:
 def __init__(self, mode=False, cap=19, maxdepth=3, maxnodes=100000, seconds=60):
  self.mode=mode;self.cap=cap;self.maxdepth=maxdepth;self.maxnodes=maxnodes;self.seconds=seconds
  self.start=time.monotonic();self.nodes=0;self.steps=0;self.cardprune=0;self.coverprune=0;self.cofprune=0;self.seen={};self.bylevel={};self.frontier=[];self.lastreport=self.start
  self.positive=[(1<<a)|(1<<b)for a,b in E]
  ind=[r for r in range(1024)if not(TARGET>>r&1)]
  self.negative=ind if mode else [r for r in ind if all((r>>i&1)or (r|1<<i)not in ind for i in range(N))]
  self.paircount=len(self.positive)*len(self.negative);self.allcov=(1<<self.paircount)-1
  self.group=AUTOS;self.cut_fn=None
 def report(self):
  print(json.dumps(dict(nodes=self.nodes,steps=self.steps,cardprune=self.cardprune,coverprune=self.coverprune,cofprune=self.cofprune,cache=len(self.seen),levels=self.bylevel,seconds=round(time.monotonic()-self.start,2))),flush=True)
 @functools.lru_cache(300000)
 def col(self,s):
  neg=sum((s>>r&1)<<j for j,r in enumerate(self.negative)); nm=(1<<len(self.negative))-1; c=0
  for i,r in enumerate(self.positive):
   v=s>>r&1
   row=(neg^nm if v else neg)if self.mode else (neg^nm if v else 0)
   c|=row<<(i*len(self.negative))
  return c
 def canonical(self,state):
  return min(tuple(sorted(moved(v,p)for v in state))for p in self.group)
 def children(self,state,remaining,history):
  n=len(state);cols=[self.col(v)for v in state]
  union=one=two=0
  for z in cols:
   union,one,two=(union|z),((z&~union)|(one&~z)),((z&one)|(two&~z))
  assert union==self.allcov
  for i in range(n):
   a=state[i];ca=cols[i]
   for j in range(i+1,n):
    b=state[j];cb=cols[j]
    for op in range(4 if self.mode else 2):
     z=opval(op,a,b)
     if z==0 or z==FULL or z in state:continue
     cz=self.col(z)
     for ka,kb in [(False,False),(True,False),(False,True),(True,True)]:
      self.steps+=1
      if n+1-(not ka)-(not kb)>remaining:
       self.cardprune+=1;continue
      lost=0 if ka and kb else one&(cb if ka else ca if kb else ca|cb)
      if not ka and not kb:lost|=two&ca&cb
      if (union&~lost)|cz!=self.allcov:
       self.coverprune+=1;continue
      child=tuple(sorted([v for k,v in enumerate(state)if(k!=i or ka)and(k!=j or kb)]+[z]))
      yield child,(op,a,b)
 def dfs(self,state,remaining,history):
  if time.monotonic()-self.start>self.seconds or self.nodes>=self.maxnodes:raise TimeoutError
  canon=self.canonical(state);key=(remaining,canon)
  if key in self.seen:return False
  self.seen[key]=True
  self.nodes+=1;depth=self.cap-remaining;self.bylevel[depth]=self.bylevel.get(depth,0)+1
  if self.cut_fn is not None:
   cut,details=self.cut_fn(state,remaining,self.mode,history)
   if cut:self.cofprune+=1;return False
  now=time.monotonic()
  if now-self.lastreport>10:self.report();self.lastreport=now
  if TARGET in state:return history
  if depth>=self.maxdepth:
   if len(self.frontier)<1000:self.frontier.append(dict(remaining=remaining,state=[str(x)for x in state],history=[(op,str(a),str(b))for op,a,b in history]))
   return False
  for child,step in self.children(state,remaining,history):
   found=self.dfs(child,remaining-1,history+[step])
   if found:return found
  return False

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--cofactor',action='store_true');ap.add_argument('--signed',action='store_true');ap.add_argument('--cap',type=int,default=19);ap.add_argument('--depth',type=int,default=3);ap.add_argument('--nodes',type=int,default=100000);ap.add_argument('--seconds',type=int,default=60);ap.add_argument('--out',required=True);ap.add_argument('--first',choices=['andedge','andnonedge','oredge','ornonedge','diffedge','diffnonedge']);args=ap.parse_args()
 check_moves();s=Search(args.signed,args.cap,args.depth,args.nodes,args.seconds)
 if args.cofactor:
  spec=importlib.util.spec_from_file_location('cofactor_prune',str(Path(__file__).resolve().parent.parent/'cofactor/cofactor_prune.py'));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);s.cut_fn=m.prune_multi
 root=tuple(sorted(INPUTS));history=[];remaining=args.cap
 if args.first:
  op=0 if args.first.startswith('and')else 1 if args.first.startswith('or')else 2
  a=INPUTS[0];b=INPUTS[2 if 'nonedge'in args.first else 1];z=opval(op,a,b)
  root=tuple(sorted(INPUTS+(z,)));history=[(op,a,b)];remaining-=1
  s.group=[p for p in AUTOS if moved(z,p)==z]
 print('mode',s.mode,'samples',len(s.positive),len(s.negative),'group',len(s.group),flush=True)
 try:
  found=s.dfs(root,remaining,history);print('done found',bool(found),flush=True)
 except TimeoutError:print('limit reached',flush=True);found=False
 s.report();Path(args.out).write_text(json.dumps(dict(frontier=s.frontier,found=[(op,str(a),str(b))for op,a,b in found]if found else None)))
if __name__=='__main__':main()
