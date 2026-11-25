import argparse,itertools,json
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('output');p.add_argument('--family',choices=['triangle','star'],required=True)
p.add_argument('--allow-unused',action='store_true')
p.add_argument('--gates',type=int,default=8)
p.add_argument('--min-nots',type=int,choices=[0,1],default=1)
p.add_argument('--max-nots',type=int,default=3)
a=p.parse_args();n=7;s=a.gates;rows=128
supports=([[0,1,4],[0,2,5],[1,2,6],[0,3],[1,3],[2,3]] if a.family=='triangle' else [[0,1,4],[0,2,5],[0,3,6],[1,2],[1,3],[2,3]])
counter=0
F=[]
def fresh():
 global counter
 counter+=1;return counter
def one(vs):
 F.append(vs)
 for v,w in itertools.combinations(vs,2):F.append([-v,-w])
op=[[fresh() for k in range(3)] for j in range(s)]
src=[[[fresh() for k in range(n+j)] for sd in range(2)] for j in range(s)]
vals=[[[fresh() for r in range(rows)] for sd in range(3)] for j in range(s)]
outputs=[[fresh() for k in range(s)] for j in supports]
for j in range(s):
 one(op[j])
 for sd in range(2):one(src[j][sd])
 for k in range(n+j):
  F.append([-op[j][2],-src[j][0][k],src[j][1][k]])
  for l in range(k+1):F.append([-src[j][0][k],-src[j][1][l],op[j][2]])
 for r in range(rows):
  for sd in range(2):
   value=vals[j][sd][r]
   for k in range(n+j):
    select=src[j][sd][k]
    if k<n:F.append([-select,value if r>>k&1 else -value])
    else:
     old=vals[k-n][2][r]
     F.extend([[-select,-value,old],[-select,value,-old]])
  u,v,w=[vals[j][sd][r] for sd in range(3)]
  o0,o1,o2=op[j]
  F.extend([[-o0,-w,u],[-o0,-w,v],[-o0,w,-u,-v],[-o1,w,-u],[-o1,w,-v],[-o1,-w,u,v],[-o2,w,u],[-o2,-w,-u]])
for q,support in enumerate(supports):
 one(outputs[q])
 for r in range(rows):
  y=any(r>>i&1 for i in support)
  for k in range(s):F.append([-outputs[q][k],vals[k][2][r] if y else -vals[k][2][r]])
for k in range(s):
 for a1,b1 in itertools.combinations(range(6),2):F.append([-outputs[a1][k],-outputs[b1][k]])
if not a.allow_unused:
 for j in range(s):
  F.append([src[k][sd][n+j] for k in range(j+1,s) for sd in range(2)]+[out[j] for out in outputs])
if a.min_nots:F.append([op[j][2] for j in range(s)])
for js in itertools.combinations(range(s),a.max_nots+1):F.append([-op[j][2] for j in js])
with Path(a.output).open('w') as f:
 f.write(f'p cnf {counter} {len(F)}\n')
 for c in F:f.write(' '.join(map(str,c))+' 0\n')
Path(a.output+'.map.json').write_text(json.dumps({'op':op,'src':src,'vals':vals,'outputs':outputs,'supports':supports,'n':n,'s':s,'family':a.family,'allow_unused':a.allow_unused,'min_nots':a.min_nots,'max_nots':a.max_nots}))
print(a.family,'variables',counter,'clauses',len(F))
