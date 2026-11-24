import sys,json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-42/sat');rows=json.loads((base/'rows-14.json').read_text());N=int(sys.argv[1]) if len(sys.argv)>1 else 10
names={};counter=0;clauses=[]
def var(name):
 global counter
 counter+=1;names[name]=counter;return counter
def neg(x):return not x if type(x)==bool else -x
def add(*xs):
 if any(type(x)==bool and x for x in xs):return
 ys=[x for x in xs if type(x)!=bool]
 if any(-x in ys for x in ys):return
 clauses.append(list(dict.fromkeys(ys)))
values=[[bool(p>>i&1) for p,t in rows] for i in range(13)]+[[False]*len(rows)]
def conjunction(k,arg):
 sels=[var(f's{k}_{arg}_{j}') for j in range(len(values))]
 out=[]
 for r in range(len(rows)):
  z=var(f'm{k}_{arg}_{r}');out.append(z);false=[]
  for j,s in enumerate(sels):
   v=values[j][r]
   add(-z,-s,v)
   if type(v)==bool:
    if not v:false.append(s)
   else:
    bad=var(f'e{k}_{arg}_{r}_{j}');false.append(bad)
    add(-bad,s);add(-bad,-v);add(bad,-s,v)
  add(z,*false)
 return out
for k in range(N):
 a=conjunction(k,0);b=conjunction(k,1);out=[]
 for r,(x,y) in enumerate(zip(a,b)):
  z=var(f'v{k}_{r}');out.append(z)
  add(-x,z);add(-y,z);add(x,y,-z)
 values.append(out)
output=conjunction(N,0)
for r,(p,t) in enumerate(rows):add(output[r] if t else -output[r])
with (base/f'free-and-{N}.cnf').open('w') as f:
 f.write(f'p cnf {counter} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
(base/f'free-and-vars-{N}.json').write_text(json.dumps(names));print('variables',counter,'clauses',len(clauses))
