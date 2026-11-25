from pathlib import Path
import json,sys,itertools,hashlib
path=Path(sys.argv[1]);o=json.loads(path.read_text());g=o['gates'];out=o['output'];D={0,1,3,9}
assert type(out)is int and 0<=out<26+len(g)
assert o['input_count']==26
assert len(g)==o['active'];assert g[0] in [[1,0,1],[0,0,13],[1,0,13],[1,2,13]]
for i,(op,a,b) in enumerate(g):assert op in(0,1)and 0<=a<26+i and 0<=b<26+i
def ev(mask):
 w=[bool(mask>>i&1)for i in range(26)]
 for op,a,b in g:w.append((w[a]or w[b])if op else(w[a]and w[b]))
 return w[out]
pos=[(1<<p)|(1<<(13+l))for p in range(13)for l in range(13)if(p+l)%13 in D]
neg=[]
for k in range(4):
 for s in itertools.combinations(range(13),k):
  t=[l for l in range(13)if all((p+l)%13 not in D for p in s)]
  a=sum(1<<p for p in s);b=sum(1<<l for l in t);neg.extend([a|(b<<13),b|(a<<13)])
fn=sum(not ev(m)for m in pos);fp=sum(ev(m)for m in neg)
active=set();todo=[out]
while todo:
 i=todo.pop()
 if i<26:continue
 gate=i-26
 if gate in active:continue
 active.add(gate);todo.extend(g[gate][1:])
active.add(0)
assert len(active)==len(g)
unproductive=set()
for mask in neg:
 w=[bool(mask>>i&1)for i in range(26)]
 for i,(op,a,b)in enumerate(g):
  w.append((w[a]or w[b])if op else(w[a]and w[b]))
  if i in active and op==0 and w[-1]:unproductive.add(i)
if 'unproductive'in o:assert len(unproductive)==o['unproductive']
print(json.dumps({'file':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'gates':len(g),'positive_count':len(pos),'negative_count':len(neg),'fn':fn,'fp':fp,'unproductive':len(unproductive),'meets63':len(g)<=63 and fn==0 and fp==0}))
assert fn==0 and fp==0
