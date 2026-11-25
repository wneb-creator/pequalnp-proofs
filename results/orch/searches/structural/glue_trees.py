import random,time,json,sys
R=random.Random(296273)

def matching(edges):
 adj={}
 for a,b in edges:adj.setdefault(a,[]).append(b)
 mt={}
 def go(a,seen):
  for b in adj.get(a,[]):
   if b in seen:continue
   seen.add(b)
   if b not in mt or go(mt[b],seen):mt[b]=a;return True
  return False
 return sum(go(a,set()) for a in adj)

def graph(p,q):
 es=set();ps=[(a,p+b) for a in range(p) for b in range(q)];R.shuffle(ps)
 for a,b in ps:
  if not any((a,c) in es and (d,b) in es and (d,c) in es for d in range(p) if d!=a for c in range(p,p+q) if c!=b):es.add((a,b))
 return es

def make(G):
 adj={}
 for a,b in G:adj.setdefault(a,set()).add(b);adj.setdefault(b,set()).add(a)
 a=R.choice(list(adj));B=sorted(adj[a])
 if len(B)<2:return None
 B=[b for b in B if R.random()<.8]
 if len(B)<2:return None
 # Keep at least one neighbor absent from e, for equality in individual gadget.
 zero=R.choice(B);terms=set();D={tuple(sorted((a,b))) for b in B}
 def op(k,x,y):
  z=(k,*sorted((x,y),key=repr));terms.add(z);return z
 def OR(xs):
  xs=sorted(xs,key=repr)
  while len(xs)>1:
   # mostly left-associated, sometimes random association to vary sharing
   i=0 if R.random()<.8 else R.randrange(len(xs)-1)
   z=op("or",xs[i],xs[i+1]);xs=xs[:i]+[z]+xs[i+2:]
  return xs[0]
 es=[]
 for b in B:
  if b==zero:continue
  leaves=sorted(x for x in adj[b]-{a} if R.random()<.7)
  if leaves:
   es.append(op("and",("v",b),OR([("v",d) for d in leaves])))
   D.update(tuple(sorted((b,d))) for d in leaves)
 if not es:return None
 e=OR(es);bs=OR([("v",b) for b in B]);t=op("or",("v",a),e);k=op("and",t,bs)
 return terms,D,k,(a,B)

def calc(gad):
 T=set();D=set();K=set()
 for t,d,k,_ in gad:T|=t;D|=d;K.add(k)
 return len(T)+len(K)-len(D)-matching(D),len(T),len(K),len(D),matching(D)

start=time.time();count=0;best=999
for trial in range(30000):
 if time.time()-start>180:break
 p=R.randrange(3,11);q=R.randrange(3,11);G=graph(p,q);pool=[x for _ in range(30) if (x:=make(G))]
 if not pool:continue
 selected=[];score=(999,)
 for g in pool:
  z=calc(selected+[g]);count+=1
  if z[0]<best:
   best=z[0];print(json.dumps(dict(trial=trial,count=count,best=best,score=z,description=[x[3] for x in selected+[g]],seconds=time.time()-start)),flush=True)
  if z[0]<0:
   print(repr(selected+[g]),flush=True);sys.exit(0)
  if z[0]<=score[0] or R.random()<.1:selected.append(g);score=z
print(json.dumps(dict(done=True,count=count,best=best,seconds=time.time()-start)),flush=True)
