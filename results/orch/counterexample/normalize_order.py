import json,sys
from pathlib import Path
n=14
gs=[list(t) for t in json.loads(Path(sys.argv[1]).read_text())['gates']]
def key(j):
 o,a,b=gs[j]
 return max(n+j if a<0 else a,n+j if b<0 or o==2 else b)
count=0
while True:
 j=next((j for j in range(len(gs)-1) if key(j)>key(j+1)),None)
 if j is None:break
 assert (n+j) not in gs[j+1][1:]
 gs[j],gs[j+1]=gs[j+1],gs[j]
 for k in range(j+2,len(gs)):
  for pos in [1,2]:
   if gs[k][pos]==n+j:gs[k][pos]=n+j+1
   elif gs[k][pos]==n+j+1:gs[k][pos]=n+j
 count+=1
 assert count<100000
for g in gs:
 if g[0]==2:g[2]=-1
print('swaps',count,'keys',[key(j) for j in range(len(gs))])
Path(sys.argv[2]).write_text(json.dumps({'gates':gs,'swaps':count}))
