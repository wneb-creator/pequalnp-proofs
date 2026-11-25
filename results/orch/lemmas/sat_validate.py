#!/usr/bin/env python3
import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('solution');p.add_argument('--output');a=p.parse_args()
n,s=10,19
A=(1<<n)+n+s+2
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
text=Path(a.solution).read_text();positive=set()
assert 's SATISFIABLE' in text, 'model not SAT'
for line in text.splitlines():
 if line.startswith('v '):
  positive.update(int(v) for v in line.split()[1:] if int(v)>0)
def ix(kd,j,k):return (kd*(s+1)+j)*A+k+1
def selected(kd,j,count):return [k for k in range(count) if ix(kd,j,k) in positive]
gates=[]
for j in range(s):
 ops=selected(0,j,4);left=selected(1,j,n+j+1);right=selected(2,j,n+j+1)
 assert ops and left and right,(j,ops,left,right)
 gates.append((ops[0],left[0],right[0]))
output=selected(6,0,n+s+1);assert output
bad=[]
for row in range(1<<n):
 wires=[bool(row>>i&1) for i in range(n)]
 for op,u,v in gates:
  x=wires[u] if u<len(wires) else False;y=wires[v] if v<len(wires) else False
  wires.append((x and y) if op==0 else (x or y) if op==1 else True if op==2 else not x)
 got=wires[output[0]] if output[0]<len(wires) else False
 want=any((row>>u&1) and (row>>v&1) for u,v in edges)
 if got!=want:bad.append(row)
d={'gates':gates,'output':output[0],'not_count':sum(op==3 for op,_,_ in gates),'bad_rows':bad,'valid':not bad,'rows':1<<n}
print(json.dumps(d,indent=2))
if a.output:Path(a.output).write_text(json.dumps(d,indent=2)+'\n')
