import itertools,json,sys
from pathlib import Path
m=int(sys.argv[1]);kind=sys.argv[2];out=Path(sys.argv[3]);assert kind in ['mono','one_not','at_most_one_not']
n=7;rows=list(range(1<<n));E=[(0,4),(1,4),(2,5),(3,5),(4,5),(0,6),(1,6),(2,6),(3,6),(4,6),(5,6)]
clauses=[];nv=0
def new():
 global nv
 nv+=1;return nv
def neg(x):return not x if isinstance(x,bool) else -x
def clause(*args):
 z=[]
 for a in args:
  if a is True:return
  if a is False:continue
  if -a in z:return
  if a not in z:z.append(a)
 clauses.append(z)
def onehot(xs):
 clause(*xs)
 for a,b in itertools.combinations(xs,2):clause(-a,-b)
ors=[new() for i in range(m)];nots=[new() for i in range(m)]
left=[[new() for w in range(n+i)] for i in range(m)]
right=[[new() for w in range(n+i)] for i in range(m)]
vals=[[new() for x in rows] for i in range(m)]
outs=[new() for i in range(m)];onehot(outs)
for a,b in itertools.combinations(nots,2):clause(-a,-b)
if kind=='mono':
 for z in nots:clause(-z)
elif kind=='one_not':clause(*nots)
def val(w,r):return bool(rows[r]>>w&1) if w<n else vals[w-n][r]
for i in range(m):
 onehot(left[i]);onehot(right[i]);N=nots[i];O=ors[i]
 clause(-N,-O);clause(-N,right[i][0])
 for a in range(n+i):
  for b in range(a):clause(N,-left[i][a],-right[i][b])
 for r,x in enumerate(rows):
  av,bv=new(),new();v=vals[i][r]
  for w in range(n+i):
   q=val(w,r);aa=left[i][w];bb=right[i][w]
   clause(-aa,-av,q);clause(-aa,av,neg(q));clause(-bb,-bv,q);clause(-bb,bv,neg(q))
  clause(N,O,-v,av);clause(N,O,-v,bv);clause(N,O,v,-av,-bv)
  clause(N,-O,v,-av);clause(N,-O,v,-bv);clause(N,-O,-v,av,bv)
  clause(-N,v,av);clause(-N,-v,-av)
  target=any((x>>a&1) and (x>>b&1) for a,b in E)
  clause(-outs[i],v if target else -v)
out.with_suffix('.cnf').write_text('p cnf %d %d\n'%(nv,len(clauses))+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
out.with_suffix('.json').write_text(json.dumps(dict(n=n,m=m,kind=kind,E=E,ors=ors,nots=nots,left=left,right=right,vals=vals,outputs=outs)))
print('kind',kind,'gates',m,'vars',nv,'clauses',len(clauses),'bytes',out.with_suffix('.cnf').stat().st_size)
