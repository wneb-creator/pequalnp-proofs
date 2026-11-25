from pathlib import Path
from itertools import combinations,product
import json,random
P=Path('/tmp/oec/pequalnp-pilot-109/audit/seeds');P.mkdir(exist_ok=True)
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
n=0
for C in combinations(range(10),6):
 C=set(C)
 if not all(i in C or j in C for i,j in E):continue
 free=[(i,j) for i,j in E if i in C and j in C]
 for bits in product([0,1],repeat=len(free)):
  owned={v:[] for v in C};choices=dict(zip(free,bits));gates=[]
  def add(op,a,b):gates.append([op,a,b]);return 9+len(gates)
  for i,j in E:
   v=(j if choices[(i,j)] else i) if (i,j) in choices else i if i in C else j
   owned[v].append(j if v==i else i)
  terms=[]
  for v,ns in sorted(owned.items()):
   value=ns[0]
   for z in ns[1:]:value=add(1,value,z)
   terms.append(add(0,v,value))
  value=terms[0]
  for z in terms[1:]:value=add(1,value,z)
  assert len(gates)==20
  lines=['.model petersen','.inputs '+' '.join('x%d'%i for i in range(10)),'.outputs y']
  def name(i):return 'x%d'%i if i<10 else 'w%d'%i
  for g,(op,a,b) in enumerate(gates,10):
   lines.append('.names %s %s %s'%(name(a),name(b),name(g)))
   lines.extend(['11 1'] if op==0 else ['1- 1','-1 1'])
  lines.extend(['.names %s y'%name(value),'1 1','.end'])
  (P/('seed-%02d.blif'%n)).write_text('\n'.join(lines)+'\n')
  (P/('seed-%02d.json'%n)).write_text(json.dumps(gates)+'\n');n+=1
print('generated',n,'twenty-gate star-cover circuits')
