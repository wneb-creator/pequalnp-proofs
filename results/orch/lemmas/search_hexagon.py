import argparse
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('output')
p.add_argument('--gates',type=int,default=10)
p.add_argument('--not-count',type=int,default=1)
p.add_argument('--free-prefix',action='store_true')
a=p.parse_args()
n=6;s=a.gates;rows=64
counter=0
def fresh():
 global counter
 counter+=1
 return counter
op=[[fresh() for k in range(3)] for j in range(s)]
src=[[[fresh() for k in range(n+j)] for sd in range(2)] for j in range(s)]
vals=[[[fresh() for r in range(rows)] for sd in range(3)] for j in range(s)]
outputs=[[fresh() for k in range(n+s)] for j in range(3)] if a.free_prefix else []
F=[]
def one(vs):
 F.append(vs)
 for i,v in enumerate(vs):
  for w in vs[:i]:F.append([-v,-w])
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
  F.extend([[-o0,-w,u],[-o0,-w,v],[-o0,w,-u,-v],
            [-o1,w,-u],[-o1,w,-v],[-o1,-w,u,v],
            [-o2,w,u],[-o2,-w,-u]])
if not a.free_prefix:
 for j in range(3):F.extend([[op[j][1]],[src[j][0][j]],[src[j][1][j+3]]])
else:
 for j in range(3):
  one(outputs[j])
  for r in range(rows):
   y=bool((r>>j|r>>(j+3))&1)
   for k in range(n+s):
    if k<n:
     if bool(r>>k&1)!=y:F.append([-outputs[j][k]])
    else:F.append([-outputs[j][k],vals[k-n][2][r] if y else -vals[k-n][2][r]])
for r in range(rows):
 y=any((r>>i&r>>((i+1)%6)&1) for i in range(6))
 F.append([vals[-1][2][r] if y else -vals[-1][2][r]])
for j in range(0 if a.free_prefix else 3,s-1):
 F.append([src[k][sd][n+j] for k in range(j+1,s) for sd in range(2)]+[out[n+j] for out in outputs])
import itertools,json
if a.not_count>0:
 F.append([op[j][2] for j in range(0 if a.free_prefix else 3,s)])
 for js in itertools.combinations(range(0 if a.free_prefix else 3,s),a.not_count+1):F.append([-op[j][2] for j in js])
with Path(a.output).open('w') as f:
 f.write(f'p cnf {counter} {len(F)}\n')
 for c in F:f.write(' '.join(map(str,c))+' 0\n')
Path(a.output+'.map.json').write_text(json.dumps({'op':op,'src':src,'vals':vals,'n':n,'s':s,'outputs':outputs}))
print('variables',counter,'clauses',len(F))
