import json, sys
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-42/sat')
vals=[256463372304,8521482511360,14003410187716736,55389823206179104,155696362464215096,218994303131713984,183565875465424384,229736628136996864,270286071508729856,288160007409369088,192860064594267704,288166778660192704,283797140973809664]
target=1764784
rows=set((sum(((x>>r)&1)<<i for i,x in enumerate(vals)),(target>>r)&1) for r in range(58))
rows=sorted((p,t) for p,t in rows if not any(t==u and p!=q and ((p&q==p) if not t else (p&q==q)) for q,u in rows))
n=int(sys.argv[1]) if len(sys.argv)>1 else 14
clauses=[]; names={}; counter=0
def var(name):
 global counter
 counter+=1;names[name]=counter;return counter
def add(*xs):
 if True in (type(x)==bool and x for x in xs):return
 ys=[x for x in xs if type(x)!=bool]
 if any(-x in ys for x in ys):return
 clauses.append(list(dict.fromkeys(ys)))
def neg(x):return not x if type(x)==bool else -x
def imply_eq(s,x,y):add(-s,neg(x),y);add(-s,x,neg(y))
def exactly_one(xs):
 add(*xs)
 for i,x in enumerate(xs):
  for y in xs[i+1:]:add(-x,-y)
values={i:[bool(p>>i&1) for p,t in rows] for i in range(13)}
a={};b={};o={}
for k in range(13,13+n):
 a[k]=[var(f'a{k}_{j}') for j in range(k-1)]
 b[k]={j:var(f'b{k}_{j}') for j in range(1,k)}
 o[k]=var(f'o{k}')
 exactly_one(a[k]);exactly_one(list(b[k].values()))
 for i,x in enumerate(a[k]):
  for j,y in b[k].items():
   if i>=j:add(-x,-y)
 av=[var(f'av{k}_{r}') for r in range(len(rows))]
 bv=[var(f'bv{k}_{r}') for r in range(len(rows))]
 values[k]=[var(f'v{k}_{r}') for r in range(len(rows))]
 for j,x in enumerate(a[k]):
  for r in range(len(rows)):imply_eq(x,av[r],values[j][r])
 for j,x in b[k].items():
  for r in range(len(rows)):imply_eq(x,bv[r],values[j][r])
 for x,y,z in zip(av,bv,values[k]):
  add(-o[k],-x,z);add(-o[k],-y,z);add(-o[k],x,y,-z)
  add(o[k],x,-z);add(o[k],y,-z);add(o[k],-x,-y,z)
 # Canonical topological order sorted by greatest predecessor, then least.
 if k>13:
  for j,x in b[k-1].items():
   for i,y in b[k].items():
    if j>i:add(-x,-y)
    elif i==j:
     for h,aa in enumerate(a[k-1]):
      for g,bb in enumerate(a[k]):
       if h>g:add(-x,-y,-aa,-bb)
for r,(p,t) in enumerate(rows):add(values[12+n][r] if t else -values[12+n][r])
for k in range(13,12+n):
 add(*(list(a[j][k] for j in range(k+2,13+n))+list(b[j][k] for j in range(k+1,13+n))))
path=base/f'circuit-{n}.cnf'
with path.open('w') as f:
 f.write(f'p cnf {counter} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
(base/f'vars-{n}.json').write_text(json.dumps(names))
(base/f'rows-{n}.json').write_text(json.dumps(rows))
print('rows',len(rows),'variables',counter,'clauses',len(clauses))
